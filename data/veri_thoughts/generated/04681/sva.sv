module nios_system_alu_carry_out_assertions (
    input logic [1:0]  address,
    input logic        clk,
    input logic        in_port,
    input logic        reset_n,
    input logic [31:0] readdata
);

    // Reset forces readdata to zero.
    check_reset_clears_readdata: assert property (
        @(posedge clk) !reset_n |-> (readdata == 32'b0)
    );

    // Address 0 with in_port high updates readdata to 1 on the next cycle.
    check_addr0_high_sets_one: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00 && in_port) |=> (readdata == 32'h00000001)
    );

    // Address 0 with in_port low updates readdata to 0 on the next cycle.
    check_addr0_low_sets_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00 && !in_port) |=> (readdata == 32'h00000000)
    );

    // Any nonzero address updates readdata to 0 on the next cycle.
    check_nonzero_address_sets_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |=> (readdata == 32'h00000000)
    );

    // Active updates always clear the upper 31 bits.
    check_upper_bits_zero_after_update: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (readdata[31:1] == 31'b0)
    );

endmodule