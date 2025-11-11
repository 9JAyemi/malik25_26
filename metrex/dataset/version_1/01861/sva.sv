// SVA for combined_module
// Notes: shift_reg update on shift truncates to prior counter value by width; assertions reflect RTL semantics.

`ifndef COMBINED_MODULE_SVA
`define COMBINED_MODULE_SVA

module combined_module_sva (
  input logic         clk,
  input logic         reset,
  input logic         up_down,
  input logic         load,
  input logic         shift,
  input logic [15:0]  data_in,
  input logic [15:0]  data_out,
  input logic [15:0]  counter,
  input logic [15:0]  shift_reg
);

  default clocking cb @(posedge clk); endclocking

  // Sanity
  assert property ( !$isunknown({reset, load, shift, up_down}) );

  // Output mirrors state
  assert property ( data_out == shift_reg );

  // Full next-state mapping
  assert property (
    counter ==
      ( $past(reset) ? 16'd0 :
        $past(load)  ? $past(data_in) :
        $past(shift) ? ($past(up_down) ? $past(counter)+16'd1 : $past(counter)-16'd1) :
                       $past(counter) )
  );

  assert property (
    shift_reg ==
      ( $past(reset) ? 16'd0 :
        $past(load)  ? $past(data_in) :
        $past(shift) ? { $past(shift_reg[14:0]), $past(counter) }[15:0] : // effectively $past(counter)
                       $past(shift_reg) )
  );

  // Immediate reset effect
  assert property ( reset |-> (counter==16'd0 && shift_reg==16'd0) );

  // Priority: load dominates shift
  assert property ( $past(load && shift) |-> (counter==$past(data_in) && shift_reg==$past(data_in)) );

  // Idle holds state
  assert property ( !$past(reset) && !$past(load) && !$past(shift) |-> (counter==$past(counter) && shift_reg==$past(shift_reg)) );

  // Coverage
  cover property ( reset ##1 !reset );
  cover property ( !reset && load );
  cover property ( !reset && shift && up_down );
  cover property ( !reset && shift && !up_down );
  cover property ( $past(shift && up_down) && counter==16'h0000 && $past(counter)==16'hFFFF );   // inc wrap
  cover property ( $past(shift && !up_down) && counter==16'hFFFF && $past(counter)==16'h0000 );  // dec wrap
  cover property ( load && shift );   // priority exercised
  cover property ( !load && !shift ); // idle

endmodule

bind combined_module combined_module_sva i_combined_module_sva(
  .clk(clk),
  .reset(reset),
  .up_down(up_down),
  .load(load),
  .shift(shift),
  .data_in(data_in),
  .data_out(data_out),
  .counter(counter),
  .shift_reg(shift_reg)
);

`endif