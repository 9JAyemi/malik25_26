
module mux_add_sub (
    input [7:0] a,
    input [7:0] b,
    input select_ctrl,
    input add_sub_ctrl,
    output [3:0] Q
);

    wire [7:0] add_sub_out;
    wire mux_enable;

    // 8-bit adder/subtractor with overflow detection
    assign add_sub_out = add_sub_ctrl ? (a + b) : (a - b);

    // 4-to-1 multiplexer with enable
    assign Q = (mux_enable) ? add_sub_out[3:0] : 4'h0;

    // Enable control signal for the multiplexer
    assign mux_enable = add_sub_ctrl;

endmodule