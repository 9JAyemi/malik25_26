module assertions (
    input logic clk,
    input logic rstn,
    input logic [3:0] led,
    input logic clk_out
);

    // Clock and reset signals
    // clk: positive edge
    // rstn: active low

    // Sequential logic in grey_counter_4bit
    // q_reg increments on each positive edge of clk
    // q_reg resets to 0 when it reaches 15
    grey_counter_4bit_seq: assert property (
        @(posedge clk) disable iff (!rstn) q_reg == 4'b1111 |-> q_reg == 4'b0000
    );

    // Sequential logic in slow_oscillator
    // c_delay increments on each positive edge of osc_clk
    // c_delay resets to 0 on each negative edge of rstn
    // clk_out is the 23rd bit of c_delay
    slow_oscillator_seq: assert property (
        @(posedge osc_clk or negedge rstn) disable iff (!rstn) c_delay == 23'h000000 |-> clk_out == 1'b0
    );

    // Combinational logic in slow_oscillator
    // clk_out is the 23rd bit of c_delay
    slow_oscillator_comb: assert property (
        @(posedge osc_clk or negedge rstn) disable iff (!rstn) clk_out == c_delay[22]
    );

endmodule