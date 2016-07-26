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

#include "basic.sig".
#include "uni.sig".
#include "spi.sig".
#include "pprint.sig".

% types for process definitions
#kind def_body type.
#type def (tm -> list tm -> proc).
#type defProc (proc -> def_body).
#type defAbs  ((tm -> def_body) -> def_body).

#type simplify (proc -> proc -> o).

#type print_proc (proc -> o).

#type print_agent (agent -> o).

#type print_act (action -> o).

#type copyproc (list sub_pair -> proc -> proc -> o).

#type copyagent (list sub_pair -> agent -> agent -> o).

#type copyact (list sub_pair -> action -> action -> o).

#kind continuation type.

#type contProc (action -> proc -> list sub_pair -> continuation). 
#type contAgent (action -> agent -> list sub_pair -> continuation).
#type abscont ((name -> continuation) -> continuation). 

#type c_one (list tm -> proc -> continuation -> o).
#type c_oneAbs (list tm -> proc -> continuation -> o).
#type c_oneCon (list tm -> proc -> continuation -> o).
