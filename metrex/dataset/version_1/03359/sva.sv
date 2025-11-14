// SVA for data_converter
module data_converter_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  data_in,
  input logic [1:0]  data_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional equivalence (golden mapping)
  assert property (
    !$isunknown(data_in) |->
      data_out == ((data_in <= 4)  ? 2'b00 :
                   (data_in <= 8)  ? 2'b01 :
                   (data_in <= 12) ? 2'b10 : 2'b11)
  );

  // No X/Z on output
  assert property (!$isunknown(data_out));

  // Temporal sanity: output follows input changes monotonically and stably
  assert property (
    !$isunknown({$past(data_in),$past(data_out),data_in,data_out}) &&
    (data_in == $past(data_in)) |-> (data_out == $past(data_out))
  );

  assert property (
    !$isunknown({$past(data_in),$past(data_out),data_in,data_out}) &&
    (data_in > $past(data_in))  |-> (data_out >= $past(data_out))
  );

  assert property (
    !$isunknown({$past(data_in),$past(data_out),data_in,data_out}) &&
    (data_in < $past(data_in))  |-> (data_out <= $past(data_out))
  );

  // Functional coverage: hit each bin and boundaries
  cover property ((data_in <= 4)                   && data_out == 2'b00);
  cover property ((data_in inside {[5:8]})         && data_out == 2'b01);
  cover property ((data_in inside {[9:12]})        && data_out == 2'b10);
  cover property ((data_in inside {[13:15]})       && data_out == 2'b11);

  // Boundary step transitions
  cover property ($past(data_in)==4  && data_in==5  && $past(data_out)==2'b00 && data_out==2'b01);
  cover property ($past(data_in)==8  && data_in==9  && $past(data_out)==2'b01 && data_out==2'b10);
  cover property ($past(data_in)==12 && data_in==13 && $past(data_out)==2'b10 && data_out==2'b11);

  // Extremes
  cover property (data_in==0  && data_out==2'b00);
  cover property (data_in==15 && data_out==2'b11);

endmodule

// Example bind (provide clk/rst_n from your environment):
// bind data_converter data_converter_sva u_dc_sva (.* , .clk(clk), .rst_n(rst_n));