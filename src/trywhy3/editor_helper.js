/* Global objects */
var editor = ace.edit("editor");
editor.setTheme("ace/theme/chrome");
editor.getSession().setMode("ace/mode/why3");
var Range = ace.require("ace/range").Range;
var selectedRange = null;
var marker = null;
editor.$blockScrolling = Infinity;

function highlightError (x1, y1, x2, y2)
{
    selectedRange = new Range (x1,y1,x2,y2);
    marker = editor.session.addMarker(selectedRange, "error", "text");
}


function clearHighlight ()
{
    if (marker) {
	editor.session.removeMarker(marker);
	marker = null;
    };
}

editor.on("change", clearHighlight);

function moveToError ()
{
    if (selectedRange) {
	editor.selection.setSelectionRange(selectedRange);
	editor.moveCursorToPosition(selectedRange.start);
	selectedRange = null;
    }
}

editor.on("focus", moveToError);


function openFile ()
{
    document.getElementById("file-selector").click();
    editor.focus();
}


var loadedBuffer = "";
var loadedFilename = "";
var currentFilename = "";
var fileSelector = document.getElementById("file-selector");

function realReplaceBuffer()
{
	editor.setValue(loadedBuffer,-1);
	currentFilename = loadedFilename;
         //document.getElementById("filename_panel").innerHTML = loadedFilename;
	loadedFilename = "";
	loadedBuffer = "";
}

function confirmReplace ()
{
    realReplaceBuffer();
    document.getElementById("background-shadow").style.display = "none";
    document.getElementById("confirm-dialog").style.display = "none";
    editor.focus();
}

function cancelReplace ()
{
    loadedBuffer = "";
    loadedFilename = "";
    document.getElementById("background-shadow").style.display = "none";
    document.getElementById("confirm-dialog").style.display = "none";
    editor.focus();
}


function replaceWithLoaded()
{
    if (/\S/.test(editor.getValue())) {
	document.getElementById("background-shadow").style.display = "block";
	document.getElementById("confirm-dialog").style.display = "block";
    }
    else {
	realReplaceBuffer();
    }
    editor.focus();
}

function clearBuffer ()
{
    loadedBuffer = "";
    loadedFilename = "";
    replaceWithLoaded();
}


function realOpenFile (ev)
{
    var f = ev.target.files[0];
    if (f) {
	var r = new FileReader();
	r.onload = function(e) {
	    loadedBuffer = e.target.result;
	    loadedFilename = f.name;
	    replaceWithLoaded();
	};
	r.readAsText(f);
    };
    this.value = null;
    editor.focus();
}

fileSelector.addEventListener("change", realOpenFile, false);

var saveFile = (function ()
{
    var a = document.createElement ("a");
    document.body.appendChild(a);
    a.style.height = "0";
    a.style.width = "0";
    a.style.position = "absolute";
    a.style.top = "0";
    a.style.left = "0";
    a.style.zIndex = "-10";
    return function () {
	a.href = "data:application/octet-stream;base64," + btoa(editor.getValue()+"\n");
	a.download = /\S/.test(currentFilename) ? currentFilename : "Test.cd";
	a.click();
	editor.focus();
    };
}) ();


function standardView()
{
    var e = document.getElementById("editor");
    var c = document.getElementById("console");
    e.style.width = "100%";
    e.style.height = "60vh";
    c.style.width = "100%";
    c.style.height = "37vh";
    editor.focus();
}

function widescreenView()
{
    var e = document.getElementById("editor");
    var c = document.getElementById("console");
    e.style.width = "60%";
    e.style.height = "100%";
    c.style.width = "40%";
    c.style.height = "100%";
    editor.focus();
}


editor.focus();
