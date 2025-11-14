// SVA checker for sw_reset
module sw_reset_sva
  #(parameter int WIDTH=32, parameter int LOG2_RESET_CYCLES=8)
  (
    input  logic                      clk,
    input  logic                      resetn,
    input  logic                      slave_write,
    input  logic                      slave_waitrequest,
    input  logic                      slave_readdata,
    input  logic                      sw_reset_n_out,
    input  logic [LOG2_RESET_CYCLES:0] reset_count
  );

  localparam int SAT = 1 << LOG2_RESET_CYCLES;
  wire msb = reset_count[LOG2_RESET_CYCLES];

  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn);

  // Asynchronous reset drives counter to 0 (checked even during reset)
  a_async_reset_zero: assert property (disable iff (1'b0) (!resetn |-> reset_count == '0));

  // Simple combinational relations
  a_waitreq_def:   assert property (slave_waitrequest == !msb);
  a_readdata_def:  assert property (slave_readdata   ==  sw_reset_n_out);

  // Counter behavior
  a_count_inc:  assert property ((!slave_write && !$past(msb)) |=> reset_count == $past(reset_count)+1);
  a_count_hold: assert property (( $past(msb) && !slave_write) |=> reset_count == $past(reset_count));
  a_count_clr:  assert property (slave_write |=> reset_count == '0);

  // Output pipeline from counter MSB (3-cycle delay)
  a_out_pipe_eq:    assert property ($past(resetn,3) |-> sw_reset_n_out == $past(msb,3));
  a_msb_to_out_r:   assert property ($rose(msb)     |-> ##3 $rose(sw_reset_n_out));
  a_write_clears_o: assert property (slave_write    |-> ##3 !sw_reset_n_out);

  // Waitrequest progress and stability
  sequence no_writes_sat; !slave_write [*SAT]; endsequence
  a_wait_deasserts_after_write: assert property (slave_write ##1 no_writes_sat ##0 !slave_waitrequest);
  a_wait_stays_low_until_write: assert property (!slave_waitrequest |-> (!slave_waitrequest until (slave_write || !resetn)));

  // Coverage
  c_msb_rise:               cover property ($rose(msb));
  c_write_to_wait_low:      cover property (slave_write ##1 no_writes_sat ##0 !slave_waitrequest);
  c_write_to_out_low_high:  cover property (slave_write ##3 !sw_reset_n_out ##(SAT) $rose(msb) ##3 sw_reset_n_out);

endmodule

// Bind into DUT
bind sw_reset sw_reset_sva #(.WIDTH(WIDTH), .LOG2_RESET_CYCLES(LOG2_RESET_CYCLES))
  sw_reset_sva_i (.clk(clk),
                  .resetn(resetn),
                  .slave_write(slave_write),
                  .slave_waitrequest(slave_waitrequest),
                  .slave_readdata(slave_readdata),
                  .sw_reset_n_out(sw_reset_n_out),
                  .reset_count(reset_count));