" Vim syntax file
" Language: Ivy Model Checker
" Maintainer: Josh Jeppson
" Latest Revision: 9 November 2021

if exists("b:current_syntax")
	finish
endif

" Keywords

syn keyword ivyLang import with include export mixin using attribute

syn keyword ivyControlFlow if else for forall while decreases
syn keyword ivyControlFlow of instantiate derived
syn keyword ivyControlFlow link call after init execute
syn keyword ivyControlFlow before after around returns
syn keyword ivyControlFlow update params ensures requires modifies
syn keyword ivyControlFlow rely mixord extract some maximizing
syn keyword ivyControlFlow apply global named

syn keyword ivyObjects this instance fresh local entry macro progress autoinstance
syn keyword ivyObjects temporal tactic subclass field template process

syn keyword ivyBlocks module function individual action relation object specification
syn keyword ivyBlocks class object method destructor private public ghost implement implementation

syn keyword ivyCheck property parameter alias trusted proof require
syn keyword ivyChecks invariant variant ensure assume relation axiom 
syn keyword ivyChecks monitor exists axiom definition isolate delegate
syn keyword ivyChecks conjecture schema concept assert from theorem

syn keyword ivyTypes type nat bool int interpret state set null bv

syn keyword ivyConstants true false

" Integers (with +/- at the front)
syn match ivyNumber '[\n \t]\d\+'
syn match ivyNumber '[+-]\d\+'

" Floating points (including scientific notation)
syn match ivyNumber '[+-]\d\+\.\d*'
" TODO: Add support for scientific notation

" Strings
syn region ivyString start='"' end='"'

" Comments
syn match ivyComment "#.*$"

" Blocks
syn region ivyBlock start="{" end="}" fold transparent

" Putting it together:
let b:current_syntax = "ivy"

hi def link ivyComment 		Comment
hi def link ivyControlFlow	Statement
hi def link ivyBlocks 		Statement
hi def link ivyChecks		Statement
hi def link ivyObjects 		Type
hi def link ivyTypes 		Type
hi def link ivyNumber 		Constant
hi def link ivyString 		Constant
hi def link ivyLang			PreProc
