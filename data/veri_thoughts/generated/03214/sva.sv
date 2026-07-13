module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic [7:0] q
);

    property capture_bus;
        logic [7:0] d_sample;
        @(negedge clk) (1'b1, d_sample = d) |=> (q == d_sample);
    endproperty

    // The output bus matches the input bus sampled on the prior falling edge.
    check_capture_bus: assert property (capture_bus);

    property capture_bit0;
        logic d_sample;
        @(negedge clk) (1'b1, d_sample = d[0]) |=> (q[0] == d_sample);
    endproperty

    // Bit 0 matches the prior falling-edge sample of d[0].
    check_capture_bit0: assert property (capture_bit0);

    property capture_bit1;
        logic d_sample;
        @(negedge clk) (1'b1, d_sample = d[1]) |=> (q[1] == d_sample);
    endproperty

    // Bit 1 matches the prior falling-edge sample of d[1].
    check_capture_bit1: assert property (capture_bit1);

    property capture_bit2;
        logic d_sample;
        @(negedge clk) (1'b1, d_sample = d[2]) |=> (q[2] == d_sample);
    endproperty

    // Bit 2 matches the prior falling-edge sample of d[2].
    check_capture_bit2: assert property (capture_bit2);

    property capture_bit3;
        logic d_sample;
        @(negedge clk) (1'b1, d_sample = d[3]) |=> (q[3] == d_sample);
    endproperty

    // Bit 3 matches the prior falling-edge sample of d[3].
    check_capture_bit3: assert property (capture_bit3);

    property capture_bit4;
        logic d_sample;
        @(negedge clk) (1'b1, d_sample = d[4]) |=> (q[4] == d_sample);
    endproperty

    // Bit 4 matches the prior falling-edge sample of d[4].
    check_capture_bit4: assert property (capture_bit4);

    property capture_bit5;
        logic d_sample;
        @(negedge clk) (1'b1, d_sample = d[5]) |=> (q[5] == d_sample);
    endproperty

    // Bit 5 matches the prior falling-edge sample of d[5].
    check_capture_bit5: assert property (capture_bit5);

    property capture_bit6;
        logic d_sample;
        @(negedge clk) (1'b1, d_sample = d[6]) |=> (q[6] == d_sample);
    endproperty

    // Bit 6 matches the prior falling-edge sample of d[6].
    check_capture_bit6: assert property (capture_bit6);

    property capture_bit7;
        logic d_sample;
        @(negedge clk) (1'b1, d_sample = d[7]) |=> (q[7] == d_sample);
    endproperty

    // Bit 7 matches the prior falling-edge sample of d[7].
    check_capture_bit7: assert property (capture_bit7);

endmodule