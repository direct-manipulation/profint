var demo = {};

(function(){
var initial_form = "(\\A [x] \\E [y] r (f x) y) & (\\A [z] r (f j) z => p (f z)) => \\E [u] p (f u)";

const macros = {
  "\\o": "\\mathsf{o}",
  "\\i": "\\mathsf{i}",
  "\\lnsrc": "{\\color{orange}#1}",
  "\\lndest": "{\\color{blue}#1}",
};

const katex_options = {
  trust: true,
  output: "html",
  strict: false,
  maxExpand: Infinity,
  macros
};

const formLink = {
  src: null,
  dest: null
};

function findPath(elem) {
  var path;
  var outputDiv = $("#output");
  while (elem && !$(elem).is(outputDiv)) {
    path = $(elem).data("path");
    if (path) break;
    elem = $(elem).parent();
  }
  if (!path) path = "";
  // console.log("findPath: " + path);
  return path;
}

function clearLinks() {
  formLink.src = null;
  formLink.dest = null;
  $("#output .enclosing").removeClass("f-src");
  $("#output .enclosing").removeClass("f-dest");
}

demo.clearLinks = clearLinks;

var witnessBox = null;

function makeWitnessBoxAt(elem) {
  const path = findPath(elem)
  const txt = profint.testWitness(path);
  if (txt) {
    witnessBox = $("<input>")
      .attr("placeholder", txt)
      .attr("value", "")
      .attr("size", Math.max(txt.length, 1))
      .data("path", path)
      .css({"font-family": "monospace",
            "font-size": "inherit"})
      .on("input", function(ev){
        $(this).attr("size", Math.max(ev.target.value.length, 1));
      })
      .on("change", function(ev){
        // console.log("path: " + $(ev.target).data("path"));
        // console.log("new witness: " + ev.target.value);
        const res = profint.doWitness($(ev.target).data("path"),
                                      ev.target.value);
        if (res) {
          witnessBox = null;
          renderFormula();
        } else {
          console.log("witness was not accepted");
          witnessBox.css({"background-color": "red"})
            .animate({"background-color": "inherit"}, "slow");
        }
      })
      .on("keyup", function(ev){
        if (ev.key === "Escape") {
          witnessBox = null;
          renderFormula();
          ev.stopPropagation();
        }
      });
    $($(elem).children("span")[1]).replaceWith(witnessBox);
    witnessBox.focus();
  }
}

function makeWitnessBox() {
  if (witnessBox) {
    console.log("there is already a witness box");
    return;
  }
  var hlForm = $(".hl-range");
  if (hlForm.length != 1) {
    console.log("there is more than one hl!");
    return;
  }
  makeWitnessBoxAt(hlForm);
}

function flashRed() {
  const op = $("#output");
  const color = op.css("color");
  const backColor = op.css("background-color");
  $("#output").css({
    "color": "red",
    "background-color": "red",
  }).animate({
    "color": color,
    "background-color": backColor,
  }, "fast");
}

demo.flashRed = flashRed;

function linkSubformula(elem, copy) {
  if (witnessBox) return;
  if (formLink.src) {
    if (formLink.dest || $(elem).is(formLink.src)) {
      // do nothing
    } else {
      formLink.dest = elem;
      $(elem).addClass("f-dest");
      var res = profint.makeLink(findPath(formLink.src),
                                 findPath(formLink.dest),
                                 copy);
      if (res) renderFormula();
      else {
        console.log("link failed");
        clearLinks();
        flashRed();
      }
    }
  } else {
    formLink.src = elem;
    $(elem).addClass("f-src");
  }
}

function contractSubformula(elem) {
  var res = profint.doContraction(findPath(elem));
  if (res) renderFormula();
  else {
    console.log("contaction failed");
  }
}

function weakenSubformula(elem) {
  var res = profint.doWeakening(findPath(elem));
  if (res) renderFormula();
  else {
    console.log("weakening failed");
  }
}

function substituteWitness(elem) {
  var res = profint.doWitness(findPath(elem));
  if (res) renderFormula();
  else {
    console.log("witness failed");
  }
}

function changeFormula() {
  var text = window.prompt("Enter the new formula");
  setFormula(text);
  return false;
}

demo.changeFormula = changeFormula;

function doUndo() {
  var res = profint.doUndo();
  if (res) renderFormula();
  else flashRed(); // console.log("undo failed");
}

demo.doUndo = doUndo;

function doRedo() {
  var res = profint.doRedo();
  if (res) renderFormula();
  else flashRed(); // console.log("redo failed");
}

demo.doRedo = doRedo;

var $rmenu = undefined;

function renderFormula() {
  clearLinks();
  const output = $("#output");
  output.html(function(){
    const expr = '\\displaystyle{' + profint.getStateTeX() + '}';
    // console.log("render: " + expr);
    const rend = katex.renderToString(expr, katex_options);
    // console.log("render: " + rend);
    return rend;
  });
  $("#output .enclosing[data-path]")
    .attr("draggable", true)
    .on("contextmenu", function (ev) {
      const path = findPath(this);
      const operations = profint.getItems(path);
      // console.log(operations);
      if (operations.show) {
        $rmenu.data("attachment", this);
        $rmenu.children().css({ display: "none" });
        if (operations.contract) $("#rmenu-contract").css({ display: "block" });
        if (operations.weaken) $("#rmenu-weaken").css({ display: "block" });
        if (operations.instantiate) $("#rmenu-instantiate").css({ display: "block" });
        // if (operations.rename) $("#rmenu-rename").css({ display: "block" });
        $rmenu.css({ top: `${ev.clientY-5}px`,
                     left: `${ev.clientX-5}px` });
        $rmenu.addClass("visible");
      }
      return false;
    })
    .on("dragstart", function (ev) {
      // console.log("dragstart", this);
      if (formLink.src) {
        flashRed();
        return false;
      }
      ev.originalEvent.dataTransfer.effectAllowed = "copyMove";
      linkSubformula(this, false);
      ev.stopPropagation();
    })
    .on("dragend", function (ev) {
      // console.log("dragend", this);
      clearLinks();
      ev.stopPropagation();
    })
    .on("dragover", function(ev) {
      const de = ev.originalEvent.dataTransfer.dropEffect;
      if (de === "copy" || de === "move") {
        ev.preventDefault();
        $(this).addClass("link-droppable");
        ev.stopPropagation();
      }
    })
    .on("dragenter", function(ev) {
      ev.preventDefault();
      $(this).addClass("link-droppable");
      ev.stopPropagation();
    })
    .on("dragleave", function(ev) {
      $(this).removeClass("link-droppable");
      ev.stopPropagation();
    })
    .on("drop", function(ev) {
      // console.log("drop", this);
      const de = ev.originalEvent.dataTransfer.dropEffect;
      if (de === "copy" || de === "move") {
        // console.log("drop", de, this);
        ev.preventDefault();
        $(this).removeClass("link-droppable");
        if (!formLink.src) {
          flashRed();
          return false;
        }
        linkSubformula(this, de === "copy");
        ev.stopPropagation();
      }
    })
    .on("click", function (ev) {
      // console.log("clicked:", this);
      // if ($rmenu.hasClass("visible")
      //     && !$rmenu.is(ev.target.offsetParent)) {
      //   $rmenu.removeClass("visible");
      //   ev.stopPropagation();
      //   return false;
      // }
      if (ev.ctrlKey) {
        if (formLink.src)
          linkSubformula(this, true);
        else
          contractSubformula(this);
      }
      else if (ev.altKey) weakenSubformula(this);
      // else if (ev.shiftKey) substituteWitness(this);
      else linkSubformula(this, false);
      ev.stopPropagation();
    });
  $("#output .enclosing").mouseover(function(ev) {
    $("#output .enclosing").removeClass("hl-range");
    $(this).addClass("hl-range");
    // $("span.enclosing").css({"border-bottom": "0"});
    // $(this).css({"border-bottom": "3px solid red"});
    ev.stopPropagation();
  });
  $("#output .enclosing").mouseout(function(ev) {
    $(this).removeClass("hl-range");
    // $("span.enclosing").css({"border-bottom": "0"});
  });
  $("#output .brk").html("<br>");
  $("#output span[data-spc]").html(function(){
    // console.log('data: ', $(this).data("spc"));
    const spaces = $(this).data("spc");
    const html = '<span style="white-space:pre">' +
          ''.padEnd(spaces) + '</span>';
    // console.log(html);
    $(this).replaceWith(html);
    // $(this).css({ "white-space": "pre" })
    //   .html(''.padEnd($(this).data("spc")));
  });
  const outWidth = output.width();
  // HISTORY
  let historyCount = 0;
  $("#history").html(function(){
    let arr = profint.historyTeX();
    historyCount = arr.length;
    arr = arr.map(expr => {
      return ["<div class='elem'>",
              katex.renderToString(expr + "\\mathstrut", katex_options),
              "</div>"].join("");
    });
    return arr.join("");
  });
  $("#history > div").each(function(index) {
    if (index + 1 == historyCount) return;
    const next = $(this).next();
    if ($(this).width() > next.width()) {
      $(this).addClass("b-bot");
      next.removeClass("b-top");
    } else {
      next.addClass("b-top");
      $(this).removeClass("b-bot");
    }
  });
  if (historyCount > 0) {
    const first = $("#history > div:first-child");
    // console.log('history.width:', first.width(), outWidth);
    if (first.width() > outWidth) {
      first.addClass("b-top");
      output.removeClass("b-bot");
    } else {
      output.addClass("b-bot");
      first.removeClass("b-top");
    }
  } else
    output.removeClass("b-bot");
  $("#doUndo").prop("disabled", historyCount <= 0);
  // FUTURE
  let futureCount = 0;
  $("#future").html(function(){
    let arr = profint.futureTeX();
    futureCount = arr.length;
    arr = arr.map(expr => {
      return ["<div class='elem'>",
              katex.renderToString(expr + "\\mathstrut", katex_options),
              "</div>"].join("");
    });
    return arr.join("");
  });
  $("#future > div").each(function(index) {
    if (index == 0) return;
    const prev = $(this).prev();
    if ($(this).width() > prev.width()) {
      $(this).addClass("b-top");
      prev.removeClass("b-bot");
    } else {
      prev.addClass("b-bot");
      $(this).removeClass("b-top");
    }
  });
  if (futureCount > 0) {
    const last = $("#future > div:last-child");
    // console.log('future.width:', last.width(), outWidth);
    if (last.width() > outWidth) {
      last.addClass("b-bot");
      output.removeClass("b-top");
    } else {
      output.addClass("b-top");
      last.removeClass("b-bot");
    }
  } else
    output.removeClass("b-top");
  $("#doRedo").prop("disabled", futureCount <= 0);
  const url = new URL(document.location);
  url.searchParams.set("p", profint.getUITrace());
  history.replaceState({}, 'Profint Interface', url.href);
}

function setFormula(text) {
  var res = profint.formulaChange(text);
  if (res) renderFormula();
  else {
    // console.log("formChange() failed");
    output.css({"background-color": "red"});
    output.animate({"background-color": "white"}, "slow");
  }
}

function getProofKind() {
  return $("#proofSystem").val() || "-unknown-";
}

function copyProof() {
  var proof = profint.getProof(getProofKind());
  if (proof) {
    navigator.clipboard.writeText(proof)
      .catch(() => {
        console.error("Copy failed");
      });
  } else flashRed();
}

demo.copyProof = copyProof;

function downProof() {
  const kind = getProofKind();
  const name = $("#downName").val();
  const dirName = `${name}-${kind}`;
  const zip = profint.getProofBundle(dirName, kind);
  if (zip) {
    zip.generateAsync({ type: "blob" })
      .then((blob) => {
        saveAs(blob, `${dirName}.zip`);
      });
  } else flashRed();
}

demo.downProof = downProof;

var signatureShown = true;

function toggleSignature() {
  signatureShown = !signatureShown;
  if (signatureShown) {
    $("#signature").show();
    $("#toggleSig").html("Hide Signature");
  } else {
    $("#signature").hide();
    $("#toggleSig").html("Show Signature");
  }
}
demo.toggleSignature = toggleSignature;

function demoSetup() {
  // [START] JSZip hack
  // for below see: https://github.com/Stuk/jszip/issues/369#issuecomment-546204220
  // reset the JSZip default date
  const currDate = new Date();
  const dateWithOffset = new Date(currDate.getTime() - currDate.getTimezoneOffset() * 60000);
  JSZip.defaults.date = dateWithOffset;
  // [END] JSZip hack
  hotkeys("ctrl+up,ctrl+y,ctrl+down,ctrl+z,w,ctrl+c,n,d,escape", function (event, handler){
    switch (handler.key) {
    case "escape":
      clearLinks();
      break;
    case "ctrl+z":
    case "ctrl+down":
      doUndo();
      break;
    case "ctrl+y":
    case "ctrl+up":
      doRedo();
      break;
    case "w":
      makeWitnessBox(event);
      break;
    case 'd':
      $("#downProof").click();
      break;
    case 'ctrl+c':
      $("#copyProof").click();
      break;
    case 'n':
      $("#downName").focus().select();
      break;
    default:
      return true;
    }
    return false;
  });
  $("#interface").css({ visibility: "visible" });
  const sigText = profint.startup();
  if (!sigText) {
    demo.toggleSignature = () => {};
    $("button, select").prop("disabled", true);
    output.html("<h3><em>Invalid parameters!</em></h3><br>Could not initialize profint");
    $("#future, #history").html("");
    throw new Error("Could not initialize profint!");
  }
  renderFormula() ;
  $("#signature").html(sigText);
  var sigEditor = ace.edit("signature");
  sigEditor.setTheme("ace/theme/chrome");
  sigEditor.setOptions({
    minLines: 5,
    maxLines: 20,
    showLineNumbers: false,
    showGutter: true,
  });
  document.sigEditor = sigEditor;
  sigEditor.on("change", function(e) {
    var res = profint.signatureChange(sigEditor.getValue());
    if (!res)
      $("#signature").css({"border": "2px solid red"});
    else
      $("#signature").css({"border": "none"});
  });
  toggleSignature();
  $("#downName")
    .on("input", function(ev) {
      const txt = $(this).val();
      $(this).attr("size", txt.length);
      const isGood = txt.match(/^[a-zA-Z][a-zA-Z0-9_]*$/);
      $("#downProof").attr("disabled", !isGood);
    })
    .on("keypress", function(ev) {
      if (ev.key === "Enter") {
        ev.preventDefault();
        $(this).blur();
      }
    });
  $rmenu = $("#rmenu");
  $rmenu.on("mouseleave", (ev) => {
    $rmenu.removeClass("visible");
  });
  $rmenu.children().on("mouseup", function(ev) {
    $rmenu.removeClass("visible");
    // console.log($rmenu.data("attachment"), $(this).attr("id"));
    const elem = $rmenu.data("attachment");
    const id = $(this).attr("id");
    if (id === "rmenu-contract")
      contractSubformula(elem);
    else if (id === "rmenu-weaken")
      weakenSubformula(elem);
    else if (id === "rmenu-instantiate")
      makeWitnessBoxAt(elem);
    return false;
  });
}

demo.demoSetup = demoSetup;

function permaLink() {
  const trace = profint.getUITrace();
  let url = new URL(document.location);
  url.searchParams.set("p", trace);
  console.log("permalink:", url.href);
  // document.location.assign(url.href);
  window.open(url.href, "_blank");
}

demo.permaLink = permaLink;

})();
