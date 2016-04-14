/* Global objects */
var editor = ace.edit("editor");
var task_editor = ace.edit("task-editor");
var Range = ace.require('ace/range').Range;
editor.setTheme("ace/theme/chrome");
editor.getSession().setMode("ace/mode/why3");
editor.$blockScrolling = Infinity;

task_editor.setTheme("ace/theme/chrome");
task_editor.getSession().setMode("ace/mode/why3");
task_editor.$blockScrolling = Infinity;
task_editor.setReadOnly(true);

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
    document.getElementById("console").innerHTML = "";
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
	a.download = /\S/.test(currentFilename) ? currentFilename : "Test.mlw";
	a.click();
	editor.focus();
    };
}) ();


function standardView()
{
    var e = document.getElementById("editor-panel");
    e.classList.remove("wide-view");
    e.classList.add("standard-view");
    editor.focus();
}

function widescreenView()
{
    var e = document.getElementById("editor-panel");
    e.classList.remove("standard-view");
    e.classList.add("wide-view");


    editor.focus();
}


editor.focus();
