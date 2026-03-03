// SVA for data_converter
// Bind this module to the DUT and connect a sampling clock from the TB.
module data_converter_sva (
  input logic        clk,
  input logic [15:0] data_in,
  input logic [3:0]  data_out
);
  default clocking cb @(posedge clk); endclocking

  // Helpers that are 4-state aware
  function automatic bit any_known1_low (input logic [3:0] a);
    return (a[0]===1'b1) || (a[1]===1'b1) || (a[2]===1'b1) || (a[3]===1'b1);
  endfunction
  function automatic bit all_known0_low (input logic [3:0] a);
    return (a[0]===1'b0) && (a[1]===1'b0) && (a[2]===1'b0) && (a[3]===1'b0);
  endfunction

  // Core functional equivalence (when low nibble is known)
  assert property ( !$isunknown(data_in[3:0])
                    |-> ( data_out == ((data_in[3:0] != 4'h0) ? 4'hF : data_in[15:12]) ) );

  // If any low-nibble bit is definitively 1, output must be 4'hF
  assert property ( any_known1_low(data_in[3:0]) |-> (data_out == 4'hF) );

  // If low nibble is definitively all 0, output mirrors the high nibble (and is known)
  assert property ( all_known0_low(data_in[3:0]) |-> ((data_out === data_in[15:12]) && !$isunknown(data_out)) );

  // Output should never go X/Z
  assert property ( !$isunknown(data_out) );

  // X-optimism guard on control nibble
  assert property ( !$isunknown(data_in[3:0]) )
    else $warning("data_converter: data_in[3:0] has X/Z; 'if (data_in[3:0]!=0)' is X-optimistic");

  // Combinational stability: if input holds, output holds
  assert property ( $stable(data_in) |-> $stable(data_out) );

  // Coverage
  cover property ( any_known1_low(data_in[3:0]) && data_out == 4'hF );            // took '!=0' branch
  cover property ( all_known0_low(data_in[3:0]) && data_out === data_in[15:12] ); // took '==0' branch
  cover property ( all_known0_low(data_in[3:0]) ##1 any_known1_low(data_in[3:0]) && data_out == 4'hF ); // 0->non0
  cover property ( any_known1_low(data_in[3:0]) ##1 all_known0_low(data_in[3:0]) );                      // non0->0
endmodule

// Example bind (provide a TB clock):
// bind data_converter data_converter_sva u_data_converter_sva ( .clk(tb_clk), .data_in(data_in), .data_out(data_out) );