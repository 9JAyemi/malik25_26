// SVA for shift_register
module shift_register_sva (
  input logic        serial_in,
  input logic        shift,
  input logic [3:0]  parallel_out
);

  // Clocking
  default clocking cb @ (posedge shift); endclocking

  // Track previous-cycle sampled values and validity
  logic        past_valid = 1'b0;
  logic [3:0]  prev_po;
  logic        prev_si;
  always_ff @(posedge shift) begin
    prev_po    <= parallel_out;
    prev_si    <= serial_in;
    past_valid <= 1'b1;
  end

  // 1) Input must be known at sampling
  a_in_known: assert property (!$isunknown(serial_in))
    else $error("serial_in X/Z at posedge shift");

  // 2) Functional shift behavior on every edge
  a_shift_fn: assert property (disable iff (!past_valid || $isunknown({prev_po, prev_si, parallel_out}))
                               parallel_out == {prev_po[2:0], prev_si})
    else $error("Shift mismatch: parallel_out != {prev_po[2:0], prev_si}");

  // 3) LSB equals sampled serial_in on the edge
  a_lsb_sampled: assert property (disable iff (!past_valid || $isunknown(prev_si))
                                  parallel_out[0] == prev_si)
    else $error("LSB not equal to sampled serial_in");

  // 4) After 4 valid edges with known serial_in, contents equal last 4 samples
  int unsigned cnt = 0;
  always_ff @(posedge shift) cnt <= cnt + 1;
  a_4deep_map: assert property (disable iff (cnt < 4)
                                !$isunknown({$past(serial_in,0),
                                             $past(serial_in,1),
                                             $past(serial_in,2),
                                             $past(serial_in,3)}) |->
                                parallel_out == {$past(serial_in,3),
                                                 $past(serial_in,2),
                                                 $past(serial_in,1),
                                                 $past(serial_in,0)})
    else $error("parallel_out != last 4 serial_in samples");

  // Coverage
  c_seen_0:  cover property (serial_in == 0);
  c_seen_1:  cover property (serial_in == 1);

  sequence four_zeros; (serial_in==0) ##1 (serial_in==0) ##1 (serial_in==0) ##1 (serial_in==0); endsequence
  sequence four_ones;  (serial_in==1) ##1 (serial_in==1) ##1 (serial_in==1) ##1 (serial_in==1); endsequence
  sequence pat_1010;   (serial_in==1) ##1 (serial_in==0) ##1 (serial_in==1) ##1 (serial_in==0); endsequence

  c_zeros:  cover property (four_zeros ##0 (parallel_out == 4'b0000));
  c_ones:   cover property (four_ones  ##0 (parallel_out == 4'b1111));
  c_1010:   cover property (pat_1010  ##0 (parallel_out == 4'b1010));

endmodule

bind shift_register shift_register_sva u_shift_register_sva (
  .serial_in    (serial_in),
  .shift        (shift),
  .parallel_out (parallel_out)
);