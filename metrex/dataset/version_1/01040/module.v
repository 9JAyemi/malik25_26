module DLL (
  input ref_clk,
  input data_in,
  output reg data_out
);

parameter delay = 5; // amount of delay to be added to the reference clock signal

reg delayed_ref_clk;
reg [1:0] phase_difference;
reg [1:0] loop_filter_output;
reg [1:0] loop_filter_state;

always @(posedge ref_clk) begin
  delayed_ref_clk <= #delay ref_clk;
  phase_difference <= {phase_difference[0], data_in} ^ {delayed_ref_clk, delayed_ref_clk};
  loop_filter_output <= loop_filter_state + phase_difference;
  loop_filter_state <= loop_filter_output;
  data_out <= #delayed_ref_clk data_in;
end

endmodule