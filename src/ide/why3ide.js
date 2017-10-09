

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

function interpNotif(n) {
    if (n != null) {
        switch (n["notification"]) {
        case "None": break;
        case "Initialized" :
            printAnswer("got initialized: TODO");
            break;
        case "New_node" :
/*
            printAnswer("got new node: nid = " + n.nid + " parent = " + n.parent + " type = " + n.nodetype);
*/
            var pid ='session';
            if (n.parent != n.nid) {
                pid = "nid"+n.parent;
            }
            else {
                var session = document.getElementById(pid);
                session.innerHTML = "";
            }
            var parent = document.getElementById(pid);
            var linode = document.createElement("LI");
            var textnode = document.createTextNode(n.nodetype + " " + n.name);
            linode.appendChild(textnode);
            var ulnode = document.createElement("UL");
            ulnode.setAttribute('id',"nid"+n.nid);
            linode.appendChild(ulnode);
            parent.appendChild(linode);
            break;
        default:
            printAnswer("unsupported notification: " + n["notification"]);
        }
    }
}

function getNotification () {
var req = new XMLHttpRequest();
req.open('GET', 'http://localhost:6789/getNotifications', true);
req.onreadystatechange = function (aEvt) {
  if (req.readyState == XMLHttpRequest.DONE) {
     if(req.status == 200) {
         var r = readBody(req);
         /* printAnswer("r = |" + r + "|"); */
         var a = JSON.parse(r);
         if (a != null) {
            var l = a.length;
             /* printAnswer("length = " + l); */
            for (var n=0; n < l; n++) interpNotif(a[n])
         }
         }
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
