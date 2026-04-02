module top_module_sva (
    input wire [15:0] in,
    output wire out
);
    wire [7:0] out1;
    wire [7:0] out2;

    splitter splitter_inst(.in(in), .out1(out1), .out2(out2));
    and_gate and_gate_inst(.a(out2[0]), .b(out1[0]), .out(out));

    // out1 should always be the lower 8 bits of in
    property p_out1;
        @(posedge clk) disable iff (!reset_n) out1 == in[7:0];
    endproperty
    assert property (p_out1) else $error("out1 is not the lower 8 bits of in");

    // out2 should always be the upper 8 bits of in
    property p_out2;
        @(posedge clk) disable iff (!reset_n) out2 == in[15:8];
    endproperty
    assert property (p_out2) else $error("out2 is not the upper 8 bits of in");

    // out should be the AND of the first bits of out2 and out1
    property p_out;
        @(posedge clk) disable iff (!reset_n) out == (out2[0] & out1[0]);
    endproperty
    assert property (p_out) else $error("out is not the AND of the first bits of out2 and out1");

    // out1 should not change when in changes if reset is active
    property p_out1_reset;
        @(posedge clk) disable iff (reset_n) out1 == out1;
    endproperty
    assert property (p_out1_reset) else $error("out1 changes when in changes and reset is active");

    // out2 should not change when in changes if reset is active
    property p_out2_reset;
        @(posedge clk) disable iff (reset_n) out2 == out2;
    endproperty
    assert property (p_out2_reset) else $error("out2 changes when in changes and reset is active");

    // out should not change when in changes if reset is active
    property p_out_reset;
        @(posedge clk) disable iff (reset_n) out == out;
    endproperty
    assert property (p_out_reset) else $error("out changes when in changes and reset is active");

    // out1 should be 0 when reset is active
    property p_out1_reset_active;
        @(posedge clk) disable iff (!reset_n) out1 == 0;
    endproperty
    assert property (p_out1_reset_active) else $error("out1 is not 0 when reset is active");

    // out2 should be 0 when reset is active
    property p_out2_reset_active;
        @(posedge clk) disable iff (!reset_n) out2 == 0;
    endproperty
    assert property (p_out2_reset_active) else $error("out2 is not 0 when reset is active");

    // out should be 0 when reset is active
    property p_out_reset_active;
        @(posedge clk) disable iff (!reset_n) out == 0;
    endproperty
    assert property (p_out_reset_active) else $error("out is not 0 when reset is active");
endmodule