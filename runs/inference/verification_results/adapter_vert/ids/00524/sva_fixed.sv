module pwm_generator_sva (
    input logic clk,
    input logic pwm_out,
    input logic rst_n,
    input logic b0
);

property ResetSynceotid; @(posedge clk) (rst_n) |-> pwm_out == 1'b0 ;endproperty
assert property (ResetSynceotid);

property ClockSynceotid; @(posedge clk) (rst_n) |-> pwm_out != pwm_out ;endproperty
assert property (ClockSynceotid);

endmodule