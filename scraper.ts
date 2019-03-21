// Parses the development applications at the South Australian Wudinna District Council web site
// and places them in a database.
//
// Michael Bone
// 21th March 2019

"use strict";

import * as fs from "fs";
import * as cheerio from "cheerio";
import * as request from "request-promise-native";
import * as sqlite3 from "sqlite3";
import * as urlparser from "url";
import * as moment from "moment";
import * as pdfjs from "pdfjs-dist";
import didYouMean, * as didyoumean from "didyoumean2";

sqlite3.verbose();

const DevelopmentApplicationsUrl = "https://www.wudinna.sa.gov.au/devapprovals";
const CommentUrl = "mailto:admin@wudinna.sa.gov.au";

const Tolerance = 3;

declare const process: any;

// All valid street names, street suffixes, suburb names and hundred names.

let StreetNames = null;
let StreetSuffixes = null;
let SuburbNames = null;
let HundredNames = null;

// Sets up an sqlite database.

async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text)");
            resolve(database);
        });
    });
}

// Inserts a row in the database if the row does not already exist.

async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or ignore into [data] values (?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate
        ], function(error, row) {
            if (error) {
                console.error(error);
                reject(error);
            } else {
                if (this.changes > 0)
                    console.log(`    Inserted: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\" and received date \"${developmentApplication.receivedDate}\" into the database.`);
                else
                    console.log(`    Skipped: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\" and received date \"${developmentApplication.receivedDate}\" because it was already present in the database.`);
                sqlStatement.finalize();  // releases any locks
                resolve(row);
            }
        });
    });
}

// A 2D point.

interface Point {
    x: number,
    y: number
}

// A 2D line.

interface Line {
    x1: number,
    y1: number,
    x2: number,
    y2: number
}

// A bounding rectangle.

interface Rectangle {
    x: number,
    y: number,
    width: number,
    height: number
}

// An element (consisting of text and a bounding rectangle) in a PDF document.

interface Element extends Rectangle {
    text: string
}

// A cell in a grid (owning zero, one or more elements).

interface Cell extends Rectangle {
    elements: Element[]
}

// Gets the highest Y co-ordinate of all elements that are considered to be in the same row as
// the specified element.  Take care to avoid extremely tall elements (because these may otherwise
// be considered as part of all rows and effectively force the return value of this function to
// the same value, regardless of the value of startElement).

function getRowTop(elements: Element[], startElement: Element) {
    let top = startElement.y;
    for (let element of elements)
        if (element.y < startElement.y + startElement.height && element.y + element.height > startElement.y)  // check for overlap
            if (getVerticalOverlapPercentage(startElement, element) > 50)  // avoids extremely tall elements
                if (element.y < top)
                    top = element.y;
    return top;
}

// Constructs a rectangle based on the union of the two specified rectangles.

function union(rectangle1: Rectangle, rectangle2: Rectangle): Rectangle {
    let x = Math.min(rectangle1.x, rectangle2.x);
    let y = Math.min(rectangle1.y, rectangle1.y);
    let width = Math.max(Math.max(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width) - x, 0);
    let height = Math.max(Math.max(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height) - y, 0);
    return { x: x, y: y, width: width, height: height };
}

// Constructs a rectangle based on the intersection of the two specified rectangles.

function intersectRectangles(rectangle1: Rectangle, rectangle2: Rectangle): Rectangle {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}

// Finds the intersection point of two lines.

function intersectLines(line1: Line, line2: Line, onlyWithinLineSegments: boolean = true) : Point {
    if ((line1.x1 === line1.x2 && line1.y1 === line1.y2) || (line2.x1 === line2.x2 && line2.y1 === line2.y2))
        return undefined;  // ignore zero length lines
  
    let denominator = (line2.y2 - line2.y1) * (line1.x2 - line1.x1) - (line1.x2 - line1.x1) * (line1.y2 - line1.y1);  
    if (denominator === 0)
        return undefined;  // ignore parallel lines
  
    let distance1 = ((line2.x2 - line2.x1) * (line1.y1 - line2.y1) - (line2.y2 - line2.y1) * (line1.x1 - line2.x1)) / denominator;
    let distance2 = ((line1.x2 - line1.x1) * (line1.y1 - line2.y1) - (line1.y2 - line1.y1) * (line1.x1 - line2.x1)) / denominator;  
    if (onlyWithinLineSegments)
        if (distance1 < 0 || distance1 > 1 || distance2 < 0 || distance2 > 1)  // check that the intersection is within the line segements
            return undefined;
  
    let x = line1.x1 + distance1 * (line1.x2 - line1.x1);
    let y = line1.y1 + distance1 * (line1.y2 - line1.y1);  
    return { x: x, y: y };
}

// Rotates a rectangle 90 degrees clockwise about the origin.

function rotate90Clockwise(rectangle: Rectangle) {
    let x = -(rectangle.y + rectangle.height);
    let y = rectangle.x;
    let width = rectangle.height;
    let height = rectangle.width;
    rectangle.x = x;
    rectangle.y = y;
    rectangle.width = width;
    rectangle.height = height;
}

// Calculates the fraction of an element that lies within a cell (as a percentage).  For example,
// if a quarter of the specifed element lies within the specified cell then this would return 25.

function getPercentageOfElementInCell(element: Element, cell: Cell) {
    let elementArea = getArea(element);
    let intersectionArea = getArea(intersectRectangles(cell, element));
    return (elementArea === 0) ? 0 : ((intersectionArea * 100) / elementArea);
}

// Calculates the fraction of an element that lies within a rectangle (as a percentage).  For
// example, if a quarter of the specifed element lies within the specified rectangle then this
// would return 25.

function getPercentageOfElementInRectangle(element: Element, rectangle: Rectangle) {
    let elementArea = getArea(element);
    let intersectionArea = getArea(intersectRectangles(rectangle, element));
    return (elementArea === 0) ? 0 : ((intersectionArea * 100) / elementArea);
}

// Calculates the area of a rectangle.

function getArea(rectangle: Rectangle) {
    return rectangle.width * rectangle.height;
}

// Calculates the square of the Euclidean distance between two elements.

function calculateDistance(element1: Element, element2: Element) {
    let point1 = { x: element1.x + element1.width, y: element1.y + element1.height / 2 };
    let point2 = { x: element2.x, y: element2.y + element2.height / 2 };
    if (point2.x < point1.x - element1.width / 5)  // arbitrary overlap factor of 20% (ie. ignore elements that overlap too much in the horizontal direction)
        return Number.MAX_VALUE;
    return (point2.x - point1.x) * (point2.x - point1.x) + (point2.y - point1.y) * (point2.y - point1.y);
}

// Determines whether there is vertical overlap between two elements.

function isVerticalOverlap(element1: Element, element2: Element) {
    return element2.y < element1.y + element1.height && element2.y + element2.height > element1.y;
}

// Gets the percentage of vertical overlap between two elements (0 means no overlap and 100 means
// 100% overlap; and, for example, 20 means that 20% of the second element overlaps somewhere
// with the first element).

function getVerticalOverlapPercentage(element1: Element, element2: Element) {
    let y1 = Math.max(element1.y, element2.y);
    let y2 = Math.min(element1.y + element1.height, element2.y + element2.height);
    return (y2 < y1) ? 0 : (((y2 - y1) * 100) / element2.height);
}

// Gets the element immediately to the right of the specified element (but ignores elements that
// appear after a large horizontal gap).

function getRightElement(elements: Element[], element: Element) {
    let closestElement: Element = { text: undefined, x: Number.MAX_VALUE, y: Number.MAX_VALUE, width: 0, height: 0 };
    for (let rightElement of elements)
        if (isVerticalOverlap(element, rightElement) &&  // ensure that there is at least some vertical overlap
            getVerticalOverlapPercentage(element, rightElement) > 50 &&  // avoid extremely tall elements (ensure at least 50% overlap)
            (rightElement.x > element.x + element.width - Tolerance) &&  // ensure the element actually is to the right (approximately)
            (rightElement.x - (element.x + element.width) < 30) &&  // avoid elements that appear after a large gap (arbitrarily ensure less than a 30 pixel gap horizontally)
            calculateDistance(element, rightElement) < calculateDistance(element, closestElement))  // check if closer than any element encountered so far
            closestElement = rightElement;
    return (closestElement.text === undefined) ? undefined : closestElement;
}

// Finds the elements that most closely match the specified text and returns a rectangle that
// encompasses all of those elements.

function findTextBounds(elements: Element[], text: string) {
    // Examine all the elements on the page that being with the same character as the requested
    // text.
    
    let condensedText = text.replace(/[\s,\-_]/g, "").toLowerCase();
    let firstCharacter = condensedText.charAt(0);

    let matches = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith(firstCharacter))) {
        // Extract up to 5 elements to the right of the element that has text starting with the
        // required character (and so may be the start of the requested text).  Join together the
        // elements to the right in an attempt to find the best match to the text.

        let rightElement = element;
        let rightElements: Element[] = [];

        do {
            rightElements.push(rightElement);

            let currentText = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").toLowerCase();

            if (currentText.length > condensedText.length + 2)  // stop once the text is too long
                break;
            if (currentText.length >= condensedText.length - 2) {  // ignore until the text is close to long enough
                if (currentText === condensedText)
                    matches.push({ elements: [...rightElements], threshold: 0, text: currentText });
                else if (didYouMean(currentText, [ condensedText ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ elements: [...rightElements], threshold: 1, text: currentText });
                else if (didYouMean(currentText, [ condensedText ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true }) !== null)
                    matches.push({ elements: [...rightElements], threshold: 2, text: currentText });
            }

            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5);  // up to 5 elements
    }

    // Chose the best match (if any matches were found).  Note that trimming is performed here so
    // that text such as "  Plan" is matched in preference to text such as "plan)" (when looking
    // for elements that match "Plan").  For an example of this problem see "200/303/07" in
    // "https://www.walkerville.sa.gov.au/webdata/resources/files/DA%20Register%20-%202007.pdf".
    //
    // Note that if the match is made of several elements then sometimes the caller requires the
    // left most element and sometimes the right most element (depending on where further text
    // will be searched for relative to this "found" element).

    if (matches.length > 0) {
        let bestMatch = matches.reduce((previous, current) =>
            (previous === undefined ||
            current.threshold < previous.threshold ||
            (current.threshold === previous.threshold && Math.abs(current.text.trim().length - condensedText.length) < Math.abs(previous.text.trim().length - condensedText.length)) ? current : previous), undefined);

        // Union together the rectangles of all elements belonging to the best match.

        let rectangle = undefined;
        for (let element of bestMatch.elements)
            rectangle = (rectangle === undefined) ? element : union(rectangle, element);
        return { x: rectangle.x, y: rectangle.y, width: rectangle.width, height: rectangle.height };
    }

    return undefined;
}

// Finds the start element of each development application on the current PDF page (there are
// typically two development applications on a single page and each development application
// typically begins with the text "APPLICATION NO:").

function findStartElements(elements: Element[]) {
    const FindText = "APPLICATIONNO:";
    
    // Examine all the elements on the page that begin with the same letter as the FindText.

    let startElements: Element[] = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith(FindText.charAt(0).toLowerCase()))) {
        // Extract up to 5 elements to the right of the element that has text starting with the
        // first letter of the FindText (and so may be the start of the FindText).  Join together
        // the elements to the right in an attempt to find the best match to the FindText.

        let rightElement = element;
        let rightElements: Element[] = [];
        let matches = [];

        do {
            rightElements.push(rightElement);
        
            // Allow for common miscellaneous characters such as " ", "." and "-".

            let text = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").toLowerCase();
            if (text.length > FindText.length + 2)  // stop once the text is too long
                break;
            if (text.length >= FindText.length - 2) {  // ignore until the text is close to long enough
                if (text === FindText.toLowerCase())
                    matches.push({ element: rightElement, threshold: 0, text: text });
                else if (didYouMean(text, [ FindText ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ element: rightElement, threshold: 1, text: text });
                else if (didYouMean(text, [ FindText ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true }) !== null)
                    matches.push({ element: rightElement, threshold: 2, text: text });
            }

            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5);  // up to 5 elements

        // Chose the best match (if any matches were found).

        if (matches.length > 0) {
            let bestMatch = matches.reduce((previous, current) =>
                (previous === undefined ||
                current.threshold < previous.threshold ||
                (current.threshold === previous.threshold && Math.abs(current.text.trim().length - FindText.length) < Math.abs(previous.text.trim().length - FindText.length)) ? current : previous), undefined);
            startElements.push(bestMatch.element);
        }
    }

    // Ensure the start elements are sorted in the order that they appear on the page.

    let yComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : 0);
    startElements.sort(yComparer);
    return startElements;
}

// Parses the details from the elements associated with a single development application.

function parseApplicationElements(elements: Element[], cells: Cell[], informationUrl: string) {
    let applicationNumberHeadingBounds = findTextBounds(elements, "APPLICATION NO:");
    let descriptionHeadingCell = cells.find(cell => cell.elements.map(element => element.text).join("").replace(/\s/g, "").toUpperCase() === "DESCRIPTION:");
    let dateLodgedHeadingCell = cells.find(cell => cell.elements.map(element => element.text).join("").replace(/\s/g, "").toUpperCase() === "DATELODGED:");
    let developmentAddressHeadingCell = cells.find(cell => cell.elements.map(element => element.text).join("").replace(/\s/g, "").toUpperCase() === "DEVELOPMENTADDRESS:");

    // Get the application number.

    if (applicationNumberHeadingBounds === undefined) {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the "APPLICATION NO:" heading on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    let applicationNumberBounds = {
        x: applicationNumberHeadingBounds.x + applicationNumberHeadingBounds.width,
        y: applicationNumberHeadingBounds.y,
        width: Number.MAX_VALUE,
        height: applicationNumberHeadingBounds.height
    };
    let applicationNumber = elements.filter(element => getPercentageOfElementInRectangle(element, applicationNumberBounds) > 10).map(element => element.text).join("").replace(/\s/g, "").replace(/^:/, "");
    if (applicationNumber === undefined || applicationNumber === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the application number on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    console.log(`    Found \"${applicationNumber}\".`);

    // Get the description.
    
    let description = "";
    if (descriptionHeadingCell !== undefined) {
        let descriptionCell = cells.find(cell => (descriptionHeadingCell.x + descriptionHeadingCell.width - cell.x) ** 2 + (descriptionHeadingCell.y - cell.y) ** 2 < Tolerance ** 2);
        description = descriptionCell.elements.map(element => element.text).join("").trim().replace(/\s\s+/g, " ");
    }

    // Get the received date.
    
    let receivedDate: moment.Moment = moment.invalid();
    if (dateLodgedHeadingCell !== undefined) {
        let receivedDateCell = cells.find(cell => (dateLodgedHeadingCell.x + dateLodgedHeadingCell.width - cell.x) ** 2 + (dateLodgedHeadingCell.y - cell.y) ** 2 < Tolerance ** 2);
        let receivedDateText = receivedDateCell.elements.map(element => element.text).join("").replace(/\s/g, "");
        receivedDate = moment(receivedDateText, [ "D/M/YYYY", "D/M/YY" ], true);
    }

    // Get the address.

    if (developmentAddressHeadingCell === undefined) {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the "DEVELOPMENT ADDRESS:" heading on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }

    let addressCell = cells.find(cell => (developmentAddressHeadingCell.x + developmentAddressHeadingCell.width - cell.x) ** 2 + (developmentAddressHeadingCell.y - cell.y) ** 2 < Tolerance ** 2);
    let address = addressCell.elements.map(element => element.text).join("").trim().replace(/\s\s+/g, " ");
    if (address === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`The address is blank on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }

    // Construct the resulting application information.
       
    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description !== undefined && description.trim() !== "") ? description : "NO DESCRIPTION PROVIDED"),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: (receivedDate !== undefined && receivedDate.isValid()) ? receivedDate.format("YYYY-MM-DD") : ""
    };
}

// Examines all the lines in a page of a PDF and constructs cells (ie. rectangles) based on those
// lines.

async function parseCells(page) {
    let operators = await page.getOperatorList();

    // Find the lines.  Each line is actually constructed using a rectangle with a very short
    // height or a very narrow width.

    let lines: Rectangle[] = [];

    let previousRectangle = undefined;
    let transformStack = [];
    let transform = [ 1, 0, 0, 1, 0, 0 ];
    transformStack.push(transform);

    for (let index = 0; index < operators.fnArray.length; index++) {
        let argsArray = operators.argsArray[index];

        if (operators.fnArray[index] === pdfjs.OPS.restore)
            transform = transformStack.pop();
        else if (operators.fnArray[index] === pdfjs.OPS.save)
            transformStack.push(transform);
        else if (operators.fnArray[index] === pdfjs.OPS.transform)
            transform = pdfjs.Util.transform(transform, argsArray);
        else if (operators.fnArray[index] === pdfjs.OPS.constructPath) {
            let argumentIndex = 0;
            for (let operationIndex = 0; operationIndex < argsArray[0].length; operationIndex++) {
                if (argsArray[0][operationIndex] === pdfjs.OPS.moveTo)
                    argumentIndex += 2;
                else if (argsArray[0][operationIndex] === pdfjs.OPS.lineTo)
                    argumentIndex += 2;
                else if (argsArray[0][operationIndex] === pdfjs.OPS.rectangle) {
                    let x1 = argsArray[1][argumentIndex++];
                    let y1 = argsArray[1][argumentIndex++];
                    let width = argsArray[1][argumentIndex++];
                    let height = argsArray[1][argumentIndex++];
                    let x2 = x1 + width;
                    let y2 = y1 + height;
                    [x1, y1] = pdfjs.Util.applyTransform([x1, y1], transform);
                    [x2, y2] = pdfjs.Util.applyTransform([x2, y2], transform);
                    width = x2 - x1;
                    height = y2 - y1;
                    previousRectangle = { x: x1, y: y1, width: width, height: height };
                }
            }
        } else if ((operators.fnArray[index] === pdfjs.OPS.fill || operators.fnArray[index] === pdfjs.OPS.eoFill) && previousRectangle !== undefined) {
            lines.push(previousRectangle);
            previousRectangle = undefined;
        }
    }

    // Determine all the horizontal lines and vertical lines that make up the grid.  The following
    // is careful to ignore the short lines and small rectangles that could make up vector images
    // outside of the grid (such as a logo).  Otherwise these short lines would cause problems due
    // to the additional cells that they would cause to be constructed later.

    let horizontalLines: Line[] = [];
    let verticalLines: Line[] = [];

    for (let line of lines) {
        if (line.height <= Tolerance && line.width >= 10)  // a horizontal line
            horizontalLines.push({ x1: line.x, y1: line.y, x2: line.x + line.width, y2: line.y });
        else if (line.width <= Tolerance && line.height >= 10)  // a vertical line
            verticalLines.push({ x1: line.x, y1: line.y, x2: line.x, y2: line.y + line.height });
    }

    let horizontalLineComparer = (a: Line, b: Line) => (a.y1 > b.y1) ? 1 : ((a.y1 < b.y1) ? -1 : 0);
    horizontalLines.sort(horizontalLineComparer);
    
    let verticalLineComparer = (a: Line, b: Line) => (a.x1 > b.x1) ? 1 : ((a.x1 < b.x1) ? -1 : 0);
    verticalLines.sort(verticalLineComparer);

    // Find all horizontal lines that share a start or end point with a vertical line or that
    // intersect with a vertical line.  This purposely ignores any lines that do not intersect
    // with another line or share a start and end point (because these are often stand alone
    // lines that appear outside of any grid, perhaps as an underline underneath text).

    let points: Point[] = [];

    for (let horizontalLine of horizontalLines) {
        for (let verticalLine of verticalLines) {
            let intersectionPoint = intersectLines(horizontalLine, verticalLine, true);  // do not extend lines to infinity (there are no gaps in the lines so this is not needed)

            let haveSharedPoints =
                (verticalLine.x1 - horizontalLine.x1) ** 2 + (verticalLine.y1 - horizontalLine.y1) ** 2 < Tolerance ** 2 ||
                (verticalLine.x1 - horizontalLine.x2) ** 2 + (verticalLine.y1 - horizontalLine.y2) ** 2 < Tolerance ** 2 ||
                (verticalLine.x2 - horizontalLine.x1) ** 2 + (verticalLine.y2 - horizontalLine.y1) ** 2 < Tolerance ** 2 ||
                (verticalLine.x2 - horizontalLine.x2) ** 2 + (verticalLine.y2 - horizontalLine.y2) ** 2 < Tolerance ** 2;

            if (intersectionPoint !== undefined)
                if (!points.some(point => (intersectionPoint.x - point.x) ** 2 + (intersectionPoint.y - point.y) ** 2 < Tolerance ** 2))
                    points.push(intersectionPoint);

            if (haveSharedPoints || intersectionPoint !== undefined) {
                if (!points.some(point => (horizontalLine.x1 - point.x) ** 2 + (horizontalLine.y1 - point.y) ** 2 < Tolerance ** 2))
                    points.push({ x: horizontalLine.x1, y: horizontalLine.y1 });
                if (!points.some(point => (horizontalLine.x2 - point.x) ** 2 + (horizontalLine.y2 - point.y) ** 2 < Tolerance ** 2))
                    points.push({ x: horizontalLine.x2, y: horizontalLine.y2 });
                if (!points.some(point => (verticalLine.x1 - point.x) ** 2 + (verticalLine.y1 - point.y) ** 2 < Tolerance ** 2))
                    points.push({ x: verticalLine.x1, y: verticalLine.y1 });
                if (!points.some(point => (verticalLine.x2 - point.x) ** 2 + (verticalLine.y2 - point.y) ** 2 < Tolerance ** 2))
                    points.push({ x: verticalLine.x2, y: verticalLine.y2 });
            }
        }
    }

    // Construct cells based on the grid of points.

    let cells: Cell[] = [];

    for (let point of points) {
        // Find the next closest point in the X direction (moving across horizontally with
        // approximately the same Y co-ordinate).

        let closestRightPoint = points.reduce(((previous, current) => (Math.abs(current.y - point.y) < Tolerance && current.x > point.x && (previous === undefined || (current.x - point.x < previous.x - point.x))) ? current : previous), undefined);

        // Find the next closest point in the Y direction (moving down vertically with
        // approximately the same X co-ordinate).

        let closestDownPoint = points.reduce(((previous, current) => (Math.abs(current.x - point.x) < Tolerance && current.y > point.y && (previous === undefined || (current.y - point.y < previous.y - point.y))) ? current : previous), undefined);

        // Construct a rectangle from the found points.

        if (closestRightPoint !== undefined && closestDownPoint !== undefined)
            cells.push({ elements: [], x: point.x, y: point.y, width: closestRightPoint.x - point.x, height: closestDownPoint.y - point.y });
    }

    // Sort the cells by approximate Y co-ordinate and then by X co-ordinate.

    let cellComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
    cells.sort(cellComparer);

    return cells;
}

// Parses the text elements from a page of a PDF.

async function parseElements(page) {
    let textContent = await page.getTextContent();

    // Find all the text elements.

    let elements: Element[] = textContent.items.map(item => {
        let transform = item.transform;

        // Work around the issue https://github.com/mozilla/pdf.js/issues/8276 (heights are
        // exaggerated).  The problem seems to be that the height value is too large in some
        // PDFs.  Provide an alternative, more accurate height value by using a calculation
        // based on the transform matrix.

        let workaroundHeight = Math.sqrt(transform[2] * transform[2] + transform[3] * transform[3]);

        let x = transform[4];
        let y = transform[5];
        let width = item.width;
        let height = workaroundHeight;

        return { text: item.str, x: x, y: y, width: width, height: height };
    });

    return elements;
}

// Parses the development applications in the specified date range.

async function parsePdf(url: string) {
    console.log(`Reading development applications from ${url}.`);

    let developmentApplications = [];

    // Read the PDF.

    let buffer = await request({ url: url, encoding: null, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);

    // Parse the PDF.  Each page has the details of multiple applications.  Note that the PDF is
    // re-parsed on each iteration of the loop (ie. once for each page).  This then avoids large
    // memory usage by the PDF (just calling page._destroy() on each iteration of the loop appears
    // not to be enough to release all memory used by the PDF parsing).

    for (let pageIndex = 0; pageIndex < 500; pageIndex++) {  // limit to an arbitrarily large number of pages (to avoid any chance of an infinite loop)
        let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
        if (pageIndex >= pdf.numPages)
            break;

        console.log(`Reading and parsing applications from page ${pageIndex + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(pageIndex + 1);

        // Construct cells (ie. rectangles) based on the horizontal and vertical line segments
        // in the PDF page.

        let cells = await parseCells(page);

        // Construct elements based on the text in the PDF page.

        let elements = await parseElements(page);

        // Release the memory used by the PDF now that it is no longer required (it will be
        // re-parsed on the next iteration of the loop for the next page).

        await pdf.destroy();
        if (global.gc)
            global.gc();

        // The co-ordinate system used in a PDF is typically "upside down" so invert the
        // co-ordinates (and so this makes the subsequent logic easier to understand).

        for (let cell of cells)
            cell.y = -(cell.y + cell.height);

        for (let element of elements)
            element.y = -(element.y + element.height);

        if (page.rotate !== 0)  // degrees
            console.log(`Page is rotated ${page.rotate}°.`);

        if (page.rotate === 90) {  // degrees
            for (let cell of cells)
                rotate90Clockwise(cell);
            for (let element of elements) {
                rotate90Clockwise(element);
                [ element.y, element.width, element.height ] = [ element.y - element.width, element.height, element.width ];  // artificial adjustment (based on experimentation)
            }
        }

        // Sort the cells by approximate Y co-ordinate and then by X co-ordinate.

        let cellComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
        cells.sort(cellComparer);

        // Sort the text elements by approximate Y co-ordinate and then by X co-ordinate.

        let elementComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
        elements.sort(elementComparer);

        // Allocate each element to an "owning" cell.

        for (let element of elements) {
            let ownerCell = cells.find(cell => getPercentageOfElementInCell(element, cell) > 50);  // at least 50% of the element must be within the cell deemed to be the owner
            if (ownerCell !== undefined)
                ownerCell.elements.push(element);
        }

        // Group the elements and the cells into sections based on where the "APPLICATION NO:" text
        // starts.

        let applicationElementGroups = [];
        let startElements = findStartElements(elements);
        for (let index = 0; index < startElements.length; index++) {
            // Determine the highest Y co-ordinate of this row and the next row (or the bottom of
            // the current page).  Allow some leeway vertically (add some extra height) because
            // in some cases required elements might be higher up than the start element.
            
            let startElement = startElements[index];
            let raisedStartElement: Element = {
                text: startElement.text,
                x: startElement.x,
                y: startElement.y - startElement.height / 2,  // leeway
                width: startElement.width,
                height: startElement.height };
            let rowTop = getRowTop(elements, raisedStartElement);
            let nextRowTop = (index + 1 < startElements.length) ? getRowTop(elements, startElements[index + 1]) : Number.MAX_VALUE;

            // Extract all elements and cells between the two rows.

            applicationElementGroups.push({
                 startElement: startElements[index],
                 elements: elements.filter(element => element.y >= rowTop && element.y + element.height < nextRowTop),
                 cells: cells.filter(cell => cell.y >= rowTop && cell.y + cell.height < nextRowTop)
            });
        }

        // Parse the development application from each group of elements (ie. a section of the
        // current page of the PDF document).

        for (let applicationElementGroup of applicationElementGroups) {
            let developmentApplication = parseApplicationElements(applicationElementGroup.elements, applicationElementGroup.cells, url);
            if (developmentApplication !== undefined)
                if (!developmentApplications.some(otherDevelopmentApplication => otherDevelopmentApplication.applicationNumber === developmentApplication.applicationNumber))  // ignore duplicates
                    developmentApplications.push(developmentApplication);
        }
    }

    return developmentApplications;
}

// Gets a random integer in the specified range: [minimum, maximum).

function getRandom(minimum: number, maximum: number) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}

// Pauses for the specified number of milliseconds.

function sleep(milliseconds: number) {
    return new Promise(resolve => setTimeout(resolve, milliseconds));
}

// Parses the development applications.

async function main() {
    // Ensure that the database exists.

    let database = await initializeDatabase();

    // Read the files containing all possible street names, street suffixes, suburb names and
    // hundred names.

    StreetNames = {};
    for (let line of fs.readFileSync("streetnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetNameTokens = line.toUpperCase().split(",");
        let streetName = streetNameTokens[0].trim();
        let suburbName = streetNameTokens[1].trim();
        (StreetNames[streetName] || (StreetNames[streetName] = [])).push(suburbName);  // several suburbs may exist for the same street name
    }

    StreetSuffixes = {};
    for (let line of fs.readFileSync("streetsuffixes.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetSuffixTokens = line.toUpperCase().split(",");
        StreetSuffixes[streetSuffixTokens[0].trim()] = streetSuffixTokens[1].trim();
    }

    SuburbNames = {};
    for (let line of fs.readFileSync("suburbnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let suburbTokens = line.toUpperCase().split(",");
        SuburbNames[suburbTokens[0].trim()] = suburbTokens[1].trim();
    }

    HundredNames = [];
    for (let line of fs.readFileSync("hundrednames.txt").toString().replace(/\r/g, "").trim().split("\n"))
        HundredNames.push(line.trim().toUpperCase());

    // Read the main page of development applications.

    console.log(`Retrieving page: ${DevelopmentApplicationsUrl}`);

    let body = await request({ url: DevelopmentApplicationsUrl, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);

    let pdfUrls: string[] = [];
    for (let element of $("div.unityHtmlArticle p a").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl).href
        if (pdfUrl.toLowerCase().includes("register") && pdfUrl.toLowerCase().includes(".pdf"))
            if (!pdfUrls.some(url => url === pdfUrl))
                pdfUrls.push(pdfUrl);
    }

    // Always parse the most recent PDF file and randomly select one other PDF file to parse.

    if (pdfUrls.length === 0) {
        console.log("No PDF files were found on the page.");
        return;
    }

    console.log(`Found ${pdfUrls.length} PDF file(s).  Selecting two to parse.`);

    // Select the most recent PDF.  And randomly select one other PDF (avoid processing all PDFs
    // at once because this may use too much memory, resulting in morph.io terminating the current
    // process).

    let selectedPdfUrls: string[] = [];
    selectedPdfUrls.push(pdfUrls.pop());
    if (pdfUrls.length > 0)
        selectedPdfUrls.push(pdfUrls[getRandom(0, pdfUrls.length)]);
    if (getRandom(0, 2) === 0)
        selectedPdfUrls.reverse();

    for (let pdfUrl of selectedPdfUrls) {
        console.log(`Parsing document: ${pdfUrl}`);
        let developmentApplications = await parsePdf(pdfUrl);
        console.log(`Parsed ${developmentApplications.length} development application(s) from document: ${pdfUrl}`);

        // Attempt to avoid reaching 512 MB memory usage (this will otherwise result in the
        // current process being terminated by morph.io).

        if (global.gc)
            global.gc();

        console.log(`Inserting development applications into the database.`);
        for (let developmentApplication of developmentApplications)
            await insertRow(database, developmentApplication);
    }
}

main().then(() => console.log("Complete.")).catch(error => console.error(error));
