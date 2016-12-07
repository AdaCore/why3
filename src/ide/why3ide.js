

function printAnswer (s) {
var node = document.createElement("P");
var textnode = document.createTextNode(s);
node.appendChild(textnode);
document.getElementById('answers').appendChild(node);
}

function readBody(xhr) {
    var data;
    if (!xhr.responseType || xhr.responseType === "text") {
        data = xhr.responseText;
    } else if (xhr.responseType === "document") {
        data = xhr.responseXML;
    } else {
        data = xhr.response;
    }
    return data;
}

function getNotification () {
var req = new XMLHttpRequest();
req.open('GET', 'http://localhost:6789/getNotifications', true);
req.onreadystatechange = function (aEvt) {
  if (req.readyState == XMLHttpRequest.DONE) {
     if(req.status == 200)
      printAnswer("" + readBody(req));
     else
      printAnswer("Erreur " + req.status);
  }
};
req.send(null);
}

var notifHandler = null;

function startNotificationHandler() {
  if (notifHandler == null) {
   notifHandler = setInterval(getNotification,1000);
  }
}

function stopNotificationHandler() {
  if (notifHandler != null) {
   clearInterval(notifHandler);
   notifHandler = null;
  }
}

function sendRequest(r) {
var req = new XMLHttpRequest();
req.open('GET', 'http://localhost:6789/request?'+r, true);
req.overrideMimeType('text/json');
req.onreadystatechange = function (aEvt) {
  if (req.readyState == XMLHttpRequest.DONE) {
     if(req.status == 200)
      printAnswer("" + readBody(req));
     else
      printAnswer("Erreur " + req.status);
  }
};
req.send(null);
}
