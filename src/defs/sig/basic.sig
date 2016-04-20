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

% Type declarations for constants and predicates. 

#kind list (type -> type).

#type nil  (list X).
#type cons (X -> (list X) -> (list X)).

#type member (X -> (list X) -> o).

#type det_mem (X -> (list X) -> o).

#type subset ((list X) -> (list X) -> o).

#type equal  ((list X) -> (list X) -> o).

#type append ((list X) -> (list X) -> (list X) -> o).

#type rev ((list X) ->  (list X) -> (list X) -> o).
#type reverse ((list X) -> (list X) -> o).

#type select ((list X) -> X -> (list X) -> o).

#type insert (X -> (list X) -> (list X) -> o).

#type ground_list ((list X) -> (list X) -> o).

#type det_or (o -> o -> o).

#type enum ((X -> o) -> (list X) -> o).

#type enuml ((X -> Y -> o) -> (list X) -> (list Y) -> o).

#type enum_list ((X -> Y -> o) -> (list X) -> (list Y) -> o).

#type map ((X -> Y -> o) -> (list X) -> (list Y) -> o).

#type forall ((X -> o) -> (list X) -> o).

#kind num type.
#type 1 num.
#type 2 num.
#type 3 num.
#type 4 num.
#type 5 num.
