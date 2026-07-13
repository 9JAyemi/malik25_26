module two_bit_encoder_sva (
    input logic       clk,
    input logic [1:0] data,
    input logic       q
);

    // data 2'b00 drives q low.
    check_data_00_drives_q_low: assert property (
        @(posedge clk) (data == 2'b00) |-> (q == 1'b0)
    );

    // data 2'b01 drives q low.
    check_data_01_drives_q_low: assert property (
        @(posedge clk) (data == 2'b01) |-> (q == 1'b0)
    );

    // data 2'b10 drives q low.
    check_data_10_drives_q_low: assert property (
        @(posedge clk) (data == 2'b10) |-> (q == 1'b0)
    );

    // data 2'b11 drives q high.
    check_data_11_drives_q_high: assert property (
        @(posedge clk) (data == 2'b11) |-> (q == 1'b1)
    );

    // q can only be high for input 2'b11.
    check_q_high_only_for_data_11: assert property (
        @(posedge clk) (q == 1'b1) |-> (data == 2'b11)
    );

endmodule