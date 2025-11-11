// SVA checker for priority_encoder_8bit
// Sample with your environment clock `clk`
module priority_encoder_8bit_sva (
  input logic        clk,
  input logic [7:0]  code,
  input logic [2:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Known-propagation and output domain
  assert property ( !$isunknown(code) |=> !$isunknown(out) )
    else $error("priority_encoder_8bit: out is X/Z while code is known");
  assert property ( !$isunknown(out) |=> out inside {3'b000,3'b100,3'b010,3'b001} )
    else $error("priority_encoder_8bit: out illegal value");

  // Exact mapping (combinational, same-cycle)
  assert property ( code == 8'h80 |=> out == 3'b100 )
    else $error("priority_encoder_8bit: 0x80 should map to 3'b100");
  assert property ( code == 8'h40 |=> out == 3'b010 )
    else $error("priority_encoder_8bit: 0x40 should map to 3'b010");
  assert property ( code == 8'h20 |=> out == 3'b001 )
    else $error("priority_encoder_8bit: 0x20 should map to 3'b001");
  assert property ( (code != 8'h80 && code != 8'h40 && code != 8'h20) |=> out == 3'b000 )
    else $error("priority_encoder_8bit: default cases must map to 3'b000");

  // Combinational consistency: if inputs didn’t change, outputs didn’t either
  assert property ( $stable(code) |=> $stable(out) )
    else $error("priority_encoder_8bit: out changed without code changing");

  // Functional coverage
  cover property ( code == 8'h80 && out == 3'b100 );
  cover property ( code == 8'h40 && out == 3'b010 );
  cover property ( code == 8'h20 && out == 3'b001 );
  cover property ( code == 8'h00 && out == 3'b000 );                                            // none set
  cover property ( (code[7] && code[6]) && out == 3'b000 );                                     // multiple top bits
  cover property ( (code[7:5] == 3'b000) && (code[4:0] != 5'b0) && out == 3'b000 );             // lower bits only
endmodule

// Bind example (replace `clk` with your sampling clock signal visible in the bind scope)
bind priority_encoder_8bit priority_encoder_8bit_sva u_priority_encoder_8bit_sva (.clk(clk), .code(code), .out(out));