// SVA for td_mode_mapper
// Bindable, concise, full functional check plus coverage

module td_mode_mapper_sva_bind;
  bind td_mode_mapper td_mode_mapper_sva i_td_mode_mapper_sva (.*);
endmodule

module td_mode_mapper_sva (
  input  logic [2:0] ctrl,
  input  logic [3:0] td_mode
);
  // Sample on any relevant change (input or output)
  default clocking cb @(ctrl or td_mode); endclocking

  // Guard: only check when ctrl is known
  property p_ctrl_known; !$isunknown(ctrl); endproperty

  // Bit-accurate functional mapping (derived from the case table)
  // td_mode[3] = ctrl[0]
  assert property ( p_ctrl_known |-> (td_mode[3] == ctrl[0]) )
    else $error("td_mode[3] mismatch for ctrl=%b td_mode=%b", ctrl, td_mode);

  // td_mode[2] = ctrl[1]
  assert property ( p_ctrl_known |-> (td_mode[2] == ctrl[1]) )
    else $error("td_mode[2] mismatch for ctrl=%b td_mode=%b", ctrl, td_mode);

  // td_mode[1] = ctrl[2] & (ctrl[0] | ~ctrl[1])   // only 110 suppresses bit1
  assert property ( p_ctrl_known |-> (td_mode[1] == (ctrl[2] & (ctrl[0] | ~ctrl[1]))) )
    else $error("td_mode[1] mismatch for ctrl=%b td_mode=%b", ctrl, td_mode);

  // td_mode[0] = ctrl[1] & ctrl[2]
  assert property ( p_ctrl_known |-> (td_mode[0] == (ctrl[1] & ctrl[2])) )
    else $error("td_mode[0] mismatch for ctrl=%b td_mode=%b", ctrl, td_mode);

  // Output must be known when input is known
  assert property ( p_ctrl_known |-> !$isunknown(td_mode) )
    else $error("td_mode has X/Z for known ctrl=%b td_mode=%b", ctrl, td_mode);

  // Sanity: td_mode must be one of the 8 legal encodings when ctrl is known
  assert property ( p_ctrl_known |-> td_mode inside
                    {4'b0000,4'b1000,4'b0100,4'b1100,4'b0010,4'b1010,4'b0101,4'b1111} )
    else $error("td_mode illegal for ctrl=%b td_mode=%b", ctrl, td_mode);

  // Functional coverage: hit every mapping
  cover property ( ctrl==3'b000 && td_mode==4'b0000 );
  cover property ( ctrl==3'b001 && td_mode==4'b1000 );
  cover property ( ctrl==3'b010 && td_mode==4'b0100 );
  cover property ( ctrl==3'b011 && td_mode==4'b1100 );
  cover property ( ctrl==3'b100 && td_mode==4'b0010 );
  cover property ( ctrl==3'b101 && td_mode==4'b1010 );
  cover property ( ctrl==3'b110 && td_mode==4'b0101 );
  cover property ( ctrl==3'b111 && td_mode==4'b1111 );

endmodule