// SVA checker for my_mux
module my_mux_sva (
  input logic [2:0] select,
  input logic [7:0] input_data,
  input logic       output_data
);
  // Sample on any relevant change and allow combinational settle with ##0
  default clocking cb @(select or input_data or output_data); endclocking

  // Functional equivalence (when address and addressed bit are known)
  property p_mux_func;
    (!$isunknown(select) && !$isunknown(input_data[select]))
      |-> ##0 (output_data == input_data[select]);
  endproperty
  assert property (p_mux_func)
    else $error("my_mux: output_data != input_data[select] with known inputs");

  // No spurious output changes when inputs are stable
  assert property ( $stable({select,input_data}) |-> ##0 $stable(output_data) )
    else $error("my_mux: output_data changed while select/input_data stable");

  // Sanity: select should not contain X/Z (warn, as DUT would otherwise hold last value)
  assert property ( !$isunknown(select) )
    else $warning("my_mux: select contains X/Z; case has no match and output may retain old value");

  // Coverage: see each select value, and observe 0/1 propagation for each input bit
  genvar i;
  for (i = 0; i < 8; i++) begin : C
    cover property (select == i);
    cover property ( (select == i) && (input_data[i] == 1'b0) ##0 (output_data == 1'b0) );
    cover property ( (select == i) && (input_data[i] == 1'b1) ##0 (output_data == 1'b1) );
  end
endmodule

// Bind into the DUT
bind my_mux my_mux_sva u_my_mux_sva (.*);