module bcd_code_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] OUT1,
    input logic [3:0] OUT2
);

    // A=0 maps to 0,0.
    check_a0_mapping: assert property (
        @(posedge clk) (A == 4'd0) |-> ((OUT1 == 4'd0) && (OUT2 == 4'd0))
    );

    // A=1 maps to 0,1.
    check_a1_mapping: assert property (
        @(posedge clk) (A == 4'd1) |-> ((OUT1 == 4'd0) && (OUT2 == 4'd1))
    );

    // A=2 maps to 0,2.
    check_a2_mapping: assert property (
        @(posedge clk) (A == 4'd2) |-> ((OUT1 == 4'd0) && (OUT2 == 4'd2))
    );

    // A=3 maps to 0,3.
    check_a3_mapping: assert property (
        @(posedge clk) (A == 4'd3) |-> ((OUT1 == 4'd0) && (OUT2 == 4'd3))
    );

    // A=4 maps to 1,0.
    check_a4_mapping: assert property (
        @(posedge clk) (A == 4'd4) |-> ((OUT1 == 4'd1) && (OUT2 == 4'd0))
    );

    // A=5 maps to 1,1.
    check_a5_mapping: assert property (
        @(posedge clk) (A == 4'd5) |-> ((OUT1 == 4'd1) && (OUT2 == 4'd1))
    );

    // A=6 maps to 1,2.
    check_a6_mapping: assert property (
        @(posedge clk) (A == 4'd6) |-> ((OUT1 == 4'd1) && (OUT2 == 4'd2))
    );

    // A=7 maps to 1,3.
    check_a7_mapping: assert property (
        @(posedge clk) (A == 4'd7) |-> ((OUT1 == 4'd1) && (OUT2 == 4'd3))
    );

    // A=8 maps to 2,0.
    check_a8_mapping: assert property (
        @(posedge clk) (A == 4'd8) |-> ((OUT1 == 4'd2) && (OUT2 == 4'd0))
    );

    // A=9 maps to 2,1.
    check_a9_mapping: assert property (
        @(posedge clk) (A == 4'd9) |-> ((OUT1 == 4'd2) && (OUT2 == 4'd1))
    );

    // Inputs above 9 drive both outputs to zero.
    check_default_mapping: assert property (
        @(posedge clk) (A >= 4'd10) |-> ((OUT1 == 4'd0) && (OUT2 == 4'd0))
    );

endmodule