%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SPEC                                                                     
% Copyright (C) 2011 Alwen Tiu                                             
%
% This program is free software; you can redistribute it and/or modify     
% it under the terms of the GNU General Public License as published by     
% the Free Software Foundation; either version 2 of the License, or        
% (at your option) any later version.                                      
%
% This program is distributed in the hope that it will be useful,          
% but WITHOUT ANY WARRANTY; without even the implied warranty of           
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            
% GNU General Public License for more details.                             
%
% You should have received a copy of the GNU General Public License        
% along with this code; if not, write to the Free Software Foundation,     
% Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% base types for some syntactic categories

#kind name type. 
#kind tm type.
#kind proc type.
#kind agent type.
#kind action type.

% process constructors
#type par	(proc -> proc -> proc).
#type nu  	((tm -> proc) -> proc).
#type match 	(tm -> tm -> proc -> proc).
#type inp 	(tm -> (tm -> proc) -> proc).
#type outp	(tm -> tm -> proc -> proc).
#type zero	proc.
#type case	(tm -> tm -> (tm -> proc) -> proc).
#type let	(tm -> (tm -> tm -> proc) -> proc).
#type bang	(proc -> proc).

% agent constructors

#type abs	((tm -> proc) -> agent).
#type con	(tm -> proc -> agent).
#type new	((tm -> agent) -> agent).

% terms

#type 0		tm.
#type s		(tm -> tm).
#type ct	(name -> tm).
#type var	(name -> tm).
#type nm	(name -> tm).
#type bn	(tm -> tm).
#type en	(tm -> tm -> tm).
#type pr	(tm -> tm -> tm).
#type hs	(tm -> tm).
#type aen	(tm -> tm -> tm).
#type pub	(tm -> tm).
#type sign	(tm -> tm -> tm).
#type vk	(tm -> tm).

% actions

#type tau	action.
#type act	(tm -> action).

% predicates

#type red_proc	(proc -> proc -> o).
#type one	(proc -> action -> proc -> o).
#type oneAbs	(proc -> action -> agent -> o).
#type oneCon	(proc -> action -> agent -> o).
#type appAbs	(agent -> agent -> proc -> o).
#type appCon	(agent -> agent -> proc -> o).
#type mergeRight    (agent -> proc -> agent -> o).
#type mergeLeft     (agent -> proc -> agent -> o).

