function showedited(s){
    var iframe = document.getElementById("edited");
    var addr = "edited/"+s;
    iframe.src = addr;
    $("#edited").show()
}