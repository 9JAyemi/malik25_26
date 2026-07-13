module my_inverter_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must always be the inverse of A.
    check_output_is_inverted_input: assert property (
        @(posedge clk) Y == ~A
    );

    // A high input must produce a low output.
    check_high_input_drives_low_output: assert property (
        @(posedge clk) A |-> !Y
    );

    // A low input must produce a high output.
    check_low_input_drives_high_output: assert property (
        @(posedge clk) !A |-> Y
    );

endmodule