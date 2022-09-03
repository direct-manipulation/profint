// Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
// Copyright (C) 2022  Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

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
  output: 'html',
  strict: false,
  macros
};

const formLink = {
  src: null,
  dest: null
};

function findPath(elem) {
  var path;
  var outputDiv = $('#output');
  while (elem && !$(elem).is(outputDiv)) {
    path = $(elem).data('path');
    if (path) break;
    elem = $(elem).parent();
  }
  if (!path) path = '';
  // console.log('findPath: ' + path);
  return path;
}

function clearLinks() {
  formLink.src = null;
  formLink.dest = null;
  $('#output .enclosing').removeClass('f-src');
  $('#output .enclosing').removeClass('f-dest');
}

demo.clearLinks = clearLinks;

var witnessBox = null;

function makeWitnessBox(ev) {
  if (witnessBox) {
    console.log('there is already a witness box');
    return;
  }
  var hlForm = $('.hl-range');
  if (hlForm.length != 1) {
    console.log('there is more than one hl!');
    return;
  }
  const path = findPath(hlForm);
  const txt = profint.testWitness(path);
  if (txt) {
    witnessBox = $('<input>')
      .attr('placeholder', txt)
      .attr('value', '')
      .attr('size', Math.max(txt.length, 1))
      .data('path', path)
      .css({'font-family': 'monospace',
            'font-size': 'inherit'})
      .on('input', function(ev){
        $(this).attr('size', Math.max(ev.target.value.length, 1));
      })
      .on('change', function(ev){
        // console.log('path: ' + $(ev.target).data('path'));
        // console.log('new witness: ' + ev.target.value);
        const res = profint.doWitness($(ev.target).data('path'),
                                      ev.target.value);
        if (res) {
          witnessBox = null;
          renderFormula();
        } else {
          console.log('witness was not accepted');
          witnessBox.css({'background-color': 'red'})
            .animate({'background-color': 'inherit'}, 'slow');
        }
      })
      .on('keyup', function(ev){
        if (ev.key === 'Escape') {
          witnessBox = null;
          renderFormula();
          ev.stopPropagation();
        }
      });
    $('.hl-range > span:nth-child(2) > span:first-child')
      .replaceWith(witnessBox);
    witnessBox.focus();
  }
}

function flashRed() {
  const op = $('#output');
  const color = op.css('color');
  const backColor = op.css('background-color');
  $('#output').css({
    'color': 'red',
    'background-color': 'red',
  }).animate({
    'color': color,
    'background-color': backColor,
  }, 'fast');
}

demo.flashRed = flashRed;

function linkSubformula(elem, doContract) {
  if (witnessBox) return;
  if (formLink.src) {
    if (formLink.dest || $(elem).is(formLink.src)) {
      // do nothing
    } else {
      formLink.dest = elem;
      $(elem).addClass('f-dest');
      // console.log('dest: ' + findPath(elem));
      // $('#destId').text(findPath(elem));
      var res = profint.makeLink(findPath(formLink.src),
                                 findPath(formLink.dest),
                                 doContract);
      if (res) renderFormula();
      else {
        console.log('link failed');
        clearLinks();
        flashRed();
      }
    }
  } else {
    formLink.src = elem;
    $(elem).addClass('f-src');
    // console.log('src: ' + findPath(elem));
    // $('#srcId').text(findPath(elem));
  }
}

function contractSubformula(elem) {
  var res = profint.doContraction(findPath(elem));
  if (res) renderFormula();
  else {
    console.log('contaction failed');
  }
}

function weakenSubformula(elem) {
  var res = profint.doWeakening(findPath(elem));
  if (res) renderFormula();
  else {
    console.log('weakening failed');
  }
}

function substituteWitness(elem) {
  var res = profint.doWitness(findPath(elem));
  if (res) renderFormula();
  else {
    console.log('witness failed');
  }
}

function changeFormula() {
  var text = window.prompt('Enter the new formula');
  setFormula(text);
  return false;
}

demo.changeFormula = changeFormula;

function doUndo() {
  var res = profint.doUndo();
  if (res) renderFormula();
  else console.log('undo failed');
}

demo.doUndo = doUndo;

function doRedo() {
  var res = profint.doRedo();
  if (res) renderFormula();
  else console.log('redo failed');
}

demo.doRedo = doRedo;

function renderFormula() {
  clearLinks();
  $('#output').html(function(){
    const expr = profint.formulaHTML();
    // console.log('render: ' + expr);
    return katex.renderToString(expr, katex_options);
  });
  $('#output .enclosing[data-path]')
    .attr('draggable', true)
    .on('dragstart', function (ev) {
      // console.log('dragstart', this);
      if (formLink.src) {
        flashRed();
        return false;
      }
      linkSubformula(this, false);
      ev.stopPropagation();
    })
    .on('dragend', function (ev) {
      // console.log('dragend', this);
      clearLinks();
      ev.stopPropagation();
    })
    .on('dragover', function(ev) {
      ev.preventDefault();
      $(this).addClass('link-droppable');
      ev.stopPropagation();
    })
    .on('dragenter', function(ev) {
      ev.preventDefault();
      $(this).addClass('link-droppable');
      ev.stopPropagation();
    })
    .on('dragleave', function(ev) {
      $(this).removeClass('link-droppable');
      ev.stopPropagation();
    })
    .on('drop', function(ev) {
      // console.log('drop', this);
      ev.preventDefault();
      $(this).removeClass('link-droppable');
      if (!formLink.src) {
        flashRed();
        return false;
      }
      linkSubformula(this, false);
      ev.stopPropagation();
    })
    .on("click", function (ev) {
      // console.log('clicked:', this);
      if (ev.ctrlKey) {
        if (formLink.src)
          linkSubformula(this, true);
        else
          contractSubformula(this);
      }
      else if (ev.altKey) weakenSubformula(this);
      else if (ev.shiftKey) substituteWitness(this);
      else linkSubformula(this, false);
      ev.stopPropagation();
    });
  $("#output .enclosing").mouseover(function(ev) {
    $('#output .enclosing').removeClass('hl-range');
    $(this).addClass('hl-range');
    // $("span.enclosing").css({"border-bottom": "0"});
    // $(this).css({"border-bottom": "3px solid red"});
    ev.stopPropagation();
  });
  $("#output .enclosing").mouseout(function(ev) {
    $(this).removeClass('hl-range');
    // $("span.enclosing").css({"border-bottom": "0"});
  });
  $('#history').html(function(){
    const expr = profint.historyHTML();
    return katex.renderToString(expr, katex_options);
  });
  $('#doUndo').prop('disabled', profint.countHistory() <= 0);
  $('#future').html(function(){
    const expr = profint.futureHTML();
    return katex.renderToString(expr, katex_options);
  });
  $('#doRedo').prop('disabled', profint.countFuture() <= 0);
}

function setFormula(text) {
  var res = profint.formulaChange(text);
  if (res) renderFormula();
  else {
    // console.log('formChange() failed');
    $('#output').css({'background-color': 'red'});
    $('#output').animate({'background-color': 'white'}, 'slow');
  }
}

const proofSystems = {
  'lean4': {
    file: 'Proof.lean',
    comment: '/-PROOF-/\n',
  },
  'lean3': {
    file: 'src/Proof.lean',
    comment: '/-PROOF-/\n',
  },
  'coq': {
    file: 'Proof.v',
    comment: '(*PROOF*)\n',
  },
  'coq_reflect': {
    file: 'Proof.v',
    comment: '(*PROOF*)\n',
  },
};

function getProofKind() {
  return $('#proofSystem').val() || '-unknown-';
}

function copyProof() {
  var proof = profint.getProof(getProofKind());
  if (proof) {
    navigator.clipboard.writeText(proof)
      .catch(() => {
        console.error('Copy failed');
      });
  }
}

demo.copyProof = copyProof;

function downProof() {
  const kind = getProofKind();
  const proof_zip = kind + '/proof.zip';
  const psys = proofSystems[kind];
  const proof = profint.getProof(kind);
  if (proof) {
    fetch(proof_zip)
      .then((response) => {
        if (!response.ok)
          throw new Error('fetch(' + proof_zip + ') failed');
        return response.blob();
      })
      .then((blob) => {
        var zip = new JSZip();
        zip.loadAsync(blob)
          .then((zip) => {
            zip.file(psys.file).async('text')
              .then((text) => {
                text = text.replace(psys.comment, proof);
                zip.file(psys.file, text);
                zip.generateAsync({ type: 'blob' })
                  .then((blob) => {
                    saveAs(blob, 'proof.zip');
                  });
              });
          });
      })
      .catch((error) => {
        console.error('downProof:', error);
      });
  }
}

demo.downProof = downProof;

function demoSetup() {
  hotkeys('ctrl+up,ctrl+y,ctrl+down,ctrl+z,w,escape', function (event, handler){
    switch (handler.key) {
    case 'escape':
      clearLinks();
      break;
    case 'ctrl+z':
    case 'ctrl+down':
      doUndo(); break;
    case 'ctrl+y':
    case 'ctrl+up':
      doRedo(); break;
    case 'w':
      makeWitnessBox(event);
      return false;
    }
  });
  profint.signatureChange(document.sigEditor.getValue());
  if (profint.startup()) renderFormula();
  else setFormula(initial_form);
  toggleSignature();
}

demo.demoSetup = demoSetup;

})();