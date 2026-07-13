module EHRU_3_sva #(
    parameter DATA_SZ = 1,
    parameter RESET_VAL = 0
) (
    input logic             CLK,
    input logic [DATA_SZ-1:0] read_0,
    input logic [DATA_SZ-1:0] write_0,
    input logic             EN_write_0,
    input logic [DATA_SZ-1:0] read_1,
    input logic [DATA_SZ-1:0] write_1,
    input logic             EN_write_1,
    input logic [DATA_SZ-1:0] read_2,
    input logic [DATA_SZ-1:0] write_2,
    input logic             EN_write_2
);

    // read_0 reflects the previous cycle's selected write or hold value.
    check_read0_pipeline: assert property (
        @(posedge CLK)
        1'b1 |=> read_0 == $past(EN_write_0 ? write_0 : read_0)
    );

    // read_1 reflects the previous cycle's selected write or hold value.
    check_read1_pipeline: assert property (
        @(posedge CLK)
        1'b1 |=> read_1 == $past(EN_write_1 ? write_1 : read_1)
    );

    // read_2 reflects the previous cycle's selected write or hold value.
    check_read2_pipeline: assert property (
        @(posedge CLK)
        1'b1 |=> read_2 == $past(EN_write_2 ? write_2 : read_2)
    );

    // read_1 is the previous cycle's selected write or hold value of read_0.
    check_read1_from_read0: assert property (
        @(posedge CLK)
        1'b1 |=> read_1 == $past(EN_write_0 ? write_0 : read_0)
    );

    // read_2 is the previous cycle's selected write or hold value of read_1.
    check_read2_from_read1: assert property (
        @(posedge CLK)
        1'b1 |=> read_2 == $past(EN_write_1 ? write_1 : read_1)
    );

    // read_2 is the previous cycle's selected write or hold value of read_0.
    check_read2_from_read0: assert property (
        @(posedge CLK)
        1'b1 |=> read_2 == $past(EN_write_1 ? write_1 : (EN_write_0 ? write_0 : read_0))
    );

    // read_0 is the previous cycle's selected write or hold value of read_2.
    check_read0_from_read2: assert property (
        @(posedge CLK)
        1'b1 |=> read_0 == $past(EN_write_2 ? write_2 : read_2)
    );

    // read_0 is the previous cycle's selected write or hold value of read_1.
    check_read0_from_read1: assert property (
        @(posedge CLK)
        1'b1 |=> read_0 == $past(EN_write_1 ? write_1 : read_1)
    );

    // read_0 is the previous cycle's selected write or hold value of read_0.
    check_read0_from_read0: assert property (
        @(posedge CLK)
        1'b1 |=> read_0 == $past(EN_write_0 ? write_0 : read_0)
    );

    // read_1 is the previous cycle's selected write or hold value of read_2.
    check_read1_from_read2: assert property (
        @(posedge CLK)
        1'b1 |=> read_1 == $past(EN_write_2 ? write_2 : read_2)
    );

    // read_1 is the previous cycle's selected write or hold value of read_1.
    check_read1_from_read1: assert property (
        @(posedge CLK)
        1'b1 |=> read_1 == $past(EN_write_1 ? write_1 : read_1)
    );

endmodule