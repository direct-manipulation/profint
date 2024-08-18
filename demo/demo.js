var demo = {};

(function(){

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

function is_instantiable(bv) {
  return (bv.side === "L" && bv.quantifier === "forall")
    || (bv.side === "R" && bv.quantifier === "exists");
}
function is_anything(bv) {
  return true;
}

function makeWitnessBoxAt(elem, tester, handler) {
  const path = findPath(elem)
  const bv = profint.getBoundIdentifier(path);
  if (bv && tester(bv)) {
    const txt = bv.ident ;
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
        const res = handler($(ev.target).data("path"), ev.target.value);
        if (res) {
          witnessBox = null;
          renderFormula();
        } else {
          console.log("term was not accepted");
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

function makeWitnessBox(tester, handler) {
  if (witnessBox) {
    console.log("there is already a witness box");
    return;
  }
  var hlForm = $(".hl-range");
  if (hlForm.length != 1) {
    console.log("there is more than one hl!");
    return;
  }
  makeWitnessBoxAt(hlForm, tester, handler);
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

function nullifySubformula(elem) {
  var res = profint.doNullify(findPath(elem));
  if (res) renderFormula();
  else {
    console.log("nullifying failed");
  }
}

function substituteWitness(elem) {
  var res = profint.doWitness(findPath(elem));
  if (res) renderFormula();
  else {
    console.log("witness failed");
  }
}

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

const setDropEffect = !window.chrome ? ((ev) => {}) :
      (ev) => {
        if (ev.originalEvent.dataTransfer) {
          ev.originalEvent.dataTransfer.dropEffect =
            ev.originalEvent.ctrlKey ? "copy" : "move";
          console.log("setDropEffect:", ev.originalEvent.dataTransfer.dropEffect);
        } else console.log("setDropEffect: ignored");
      };

function renderFormula() {
  clearLinks();
  const output = $("#output");
  output.html(function() {
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
      if (true /* operations.show */) {
        $rmenu.data("attachment", this);
        $rmenu.children().css({ display: "none" });
        if (operations.contract) $("#rmenu-contract").css({ display: "block" });
        if (operations.weaken) $("#rmenu-weaken").css({ display: "block" });
        // if (operations.nullify)
          $("#rmenu-nullify").css({ display: "block" });
        if (operations.instantiate) $("#rmenu-instantiate").css({ display: "block" });
        if (operations.rename) $("#rmenu-rename").css({ display: "block" });
        $rmenu.css({ top: `${ev.clientY-5}px`,
                     left: `${ev.clientX-5}px` });
        // $rmenu.addClass("visible");
        $rmenu.show("fast");
      }
      return false;
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
var $toggleSig, $signature;

function toggleSignature() {
  signatureShown = !signatureShown;
  if (signatureShown) {
    $signature.css({
      display: "inline-block",
      top: $toggleSig.offset().top + $("#doUndo").outerHeight(),
      left: $toggleSig.offset().left
    }).show(50);
    $toggleSig.addClass("signature-shown");
  } else {
    $signature.hide(50);
    $toggleSig.removeClass("signature-shown");
  }
}
demo.toggleSignature = toggleSignature;

var $output;

function demoSetup() {
  // setup variables
  $toggleSig = $("#toggleSig");
  $signature = $("#signature");
  $output = $("#output");

  // [START] JSZip hack
  // for below see: https://github.com/Stuk/jszip/issues/369#issuecomment-546204220
  // reset the JSZip default date
  const currDate = new Date();
  const dateWithOffset = new Date(currDate.getTime() - currDate.getTimezoneOffset() * 60000);
  JSZip.defaults.date = dateWithOffset;
  // [END] JSZip hack
  hotkeys("ctrl+up,ctrl+y,ctrl+down,ctrl+z,r,w,ctrl+c,n,d,escape", function (event, handler){
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
      makeWitnessBox(is_instantiable, profint.doWitness);
      break;
    case "r":
      makeWitnessBox(is_anything, profint.doRename);
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
  if (!profint.startup()) {
    demo.toggleSignature = () => {};
    $("button, select").prop("disabled", true);
    output.html("<h3><em>Invalid parameters!</em></h3><br>Could not initialize profint");
    $("#future, #history").html("");
    throw new Error("Could not initialize profint!");
  }
  renderFormula() ;
  const output = $("#output");
  const nearestSubformula = (ev) => {
    let cur = $(ev.target);
    while (true) {
      if (cur.data("path")) break;
      if (cur.is(output)) return null;
      cur = cur.parent();
    }
    return cur[0];
  };
  let dragTarget = null;
  let dropEffect = "move";
  $output
    .on("drag", function (ev) {
      // console.log("drag", ev.originalEvent.ctrlKey);
      dropEffect = ev.originalEvent.ctrlKey ? "copy" : "move";
    })
    .on("dragstart", function (ev) {
      const cur = nearestSubformula(ev);
      if (!cur) return;
      // console.log("dragstart", $(cur).data("path"));
      if (formLink.src) {
        flashRed();
        return false;
      }
      ev.originalEvent.dataTransfer.effectAllowed = "all";
      dropEffect = ev.originalEvent.ctrlKey ? "copy" : "move";
      ev.originalEvent.dataTransfer.dropEffect = dropEffect;
      linkSubformula(cur, false);
    })
    .on("dragend", function (ev) {
      const cur = nearestSubformula(ev);
      if (!cur) return;
      // console.log("dragend", $(cur).data("path"));
      clearLinks();
      $("#output .enclosing[data-path]").removeClass("link-droppable");
    })
    .on("dragenter", function(ev) {
      ev.originalEvent.dataTransfer.dropEffect = dropEffect;
      const cur = nearestSubformula(ev);
      if (!cur) return;
      // console.log("dragenter", $(cur).data("path"));
      ev.preventDefault();
      if (!$(cur).is(dragTarget)) {
        $(dragTarget).removeClass("link-droppable");
        $(cur).addClass("link-droppable");
        dragTarget = cur;
      }
    })
    .on("dragleave", function(ev) {
      if ($(ev.target).is($output) && dragTarget) {
        $(dragTarget).removeClass("link-droppable");
        dragTarget = null;
      }
    })
    .on("dragover", function(ev) {
      ev.originalEvent.dataTransfer.dropEffect = dropEffect;
      const cur = nearestSubformula(ev);
      if (!cur) return;
      ev.preventDefault();      // allow drops
    })
    .on("drop", function(ev) {
      ev.originalEvent.dataTransfer.dropEffect = dropEffect;
      const cur = nearestSubformula(ev);
      if (!cur) return;
      // console.log("drop", $(cur).data("path"));
      if (!formLink.src) {
        flashRed();
        return false;
      }
      ev.stopPropagation();
      linkSubformula(cur, dropEffect === "copy");
    })
    .on("click", function(ev) {
      const cur = nearestSubformula(ev);
      if (!cur) return;
      if (ev.ctrlKey) {
        if (formLink.src) linkSubformula(cur, true);
        else contractSubformula(cur);
      } else if (ev.altKey) weakenSubformula(cur);
      else linkSubformula(cur, false);
      // allow bubbling
    })
    .on("mouseover", function(ev) {
      const cur = nearestSubformula(ev);
      if (!cur) return;
      $("#output .enclosing[data-path]").removeClass("hl-range");
      $(cur).addClass("hl-range");
      // allow bubbling
    })
    .on("mouseout", function(ev) {
      const cur = nearestSubformula(ev);
      if (!cur) return;
      $(cur).removeClass("hl-range");
      // allow bubbling
    })
  ;

  $signature.html(function() {
    const tex = profint.getSignatureTeX();
    return katex.renderToString(tex, katex_options);
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
    // $rmenu.removeClass("visible");
    $rmenu.hide("fast");
  });
  $rmenu.children().on("mouseup", function(ev) {
    // $rmenu.removeClass("visible");
    $rmenu.hide();
    // console.log($rmenu.data("attachment"), $(this).attr("id"));
    const elem = $rmenu.data("attachment");
    const id = $(this).attr("id");
    if (id === "rmenu-contract")
      contractSubformula(elem);
    else if (id === "rmenu-weaken")
      weakenSubformula(elem);
    else if (id === "rmenu-nullify")
      nullifySubformula(elem);
    else if (id === "rmenu-instantiate")
      makeWitnessBoxAt(elem, is_instantiable, profint.doWitness);
    else if (id === "rmenu-rename")
      makeWitnessBoxAt(elem, is_anything, profint.doRename);
    return false;
  });
}

demo.demoSetup = demoSetup;

function permaLink() {
  const trace = profint.getUITrace();
  let url = new URL(document.location);
  url.searchParams.set("p", trace);
  // console.log("permalink:", url.href);
  // document.location.assign(url.href);
  window.open(url.href, "_blank");
}

demo.permaLink = permaLink;

})();
