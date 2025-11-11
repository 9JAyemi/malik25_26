// SVA for sumwrap_uint16_to1_1
module sumwrap_uint16_to1_1_sva #(parameter string INSTANCE_NAME="INST") (
  input logic        CLK,
  input logic        CE,
  input logic [31:0] process_input,
  input logic [15:0] process_output
);

  default clocking cb @(posedge CLK); endclocking

  // Local definitions
  let least = process_input[15:0];
  let most  = process_input[31:16];
  let sum16 = least + most;                         // 16-bit wrap
  let sum17 = {1'b0, least} + {1'b0, most};         // 17-bit for overflow detect

  // Functional equivalence (primary check)
  assert property ( !$isunknown(process_input)
                    |-> process_output == (least == 16'd1 ? 16'h0000 : sum16) );

  // Branch-specific checks
  assert property ( !$isunknown(process_input) && least == 16'd1  |-> process_output == 16'h0000 );
  assert property ( !$isunknown(process_input) && least != 16'd1  |-> process_output == sum16 );

  // Knownness: outputs known when inputs known
  assert property ( !$isunknown(process_input) |-> !$isunknown(process_output) );

  // Combinational/stability: if input stable, output stable
  assert property ( $stable(process_input) |-> $stable(process_output) );

  // CE independence: changing CE alone must not affect output
  assert property ( $changed(CE) && $stable(process_input) |-> $stable(process_output) );

  // Coverage
  cover property ( least == 16'd1 );                                // special-case path
  cover property ( least != 16'd1 && sum17[16] == 1'b0 );           // add without wrap
  cover property ( least != 16'd1 && sum17[16] == 1'b1 );           // add with wrap
  cover property ( least != 16'd1 && sum16 == 16'h0000 );           // wrap to zero (distinct from special-case)

  // Boundary/interesting values
  cover property ( least == 16'h0000 && most == 16'h0000 );
  cover property ( least == 16'hFFFF );
  cover property ( most  == 16'hFFFF );

endmodule

bind sumwrap_uint16_to1_1
  sumwrap_uint16_to1_1_sva #(.INSTANCE_NAME(INSTANCE_NAME)) i_sumwrap_uint16_to1_1_sva (.*);