module EHRU_3_sva #(
    parameter DATA_SZ = 1
) (
    input logic                 CLK,
    input logic [DATA_SZ-1:0]   read_0,
    input logic [DATA_SZ-1:0]   write_0,
    input logic                 EN_write_0,
    input logic [DATA_SZ-1:0]   read_1,
    input logic [DATA_SZ-1:0]   write_1,
    input logic                 EN_write_1,
    input logic [DATA_SZ-1:0]   read_2,
    input logic [DATA_SZ-1:0]   write_2,
    input logic                 EN_write_2
);

    // read_0 is the muxed input selected by EN_write_0.
    check_read0_mux: assert property (
        @(posedge CLK) read_0 == (EN_write_0 ? write_0 : read_0)
    );

    // read_1 is the muxed input selected by EN_write_1.
    check_read1_mux: assert property (
        @(posedge CLK) read_1 == (EN_write_1 ? write_1 : read_1)
    );

    // read_2 is the muxed input selected by EN_write_2.
    check_read2_mux: assert property (
        @(posedge CLK) read_2 == (EN_write_2 ? write_2 : read_2)
    );

    // read_1 mirrors read_0 when EN_write_1 is low.
    check_read1_follows_read0_when_disabled: assert property (
        @(posedge CLK) !EN_write_1 |-> (read_1 == read_0)
    );

    // read_2 mirrors read_0 when EN_write_1 and EN_write_2 are low.
    check_read2_follows_read0_when_disabled: assert property (
        @(posedge CLK) (!EN_write_1 && !EN_write_2) |-> (read_2 == read_0)
    );

    // read_2 mirrors read_1 when EN_write_2 is low.
    check_read2_follows_read1_when_disabled: assert property (
        @(posedge CLK) !EN_write_2 |-> (read_2 == read_1)
    );

    // read_2 captures write_2 when all enable inputs are high.
    check_read2_captures_write2_when_all_enabled: assert property (
        @(posedge CLK) (EN_write_0 && EN_write_1 && EN_write_2) |=> (read_2 == $past(write_2))
    );

    // read_2 captures read_1 when only EN_write_2 is high.
    check_read2_captures_read1_when_en2_only: assert property (
        @(posedge CLK) (EN_write_1 && !EN_write_0 && EN_write_2) |=> (read_2 == $past(read_1))
    );

    // read_2 captures read_0 when only EN_write_1 is high.
    check_read2_captures_read0_when_en1_only: assert property (
        @(posedge CLK) (EN_write_1 && !EN_write_0 && !EN_write_2) |=> (read_2 == $past(read_0))
    );

    // read_2 captures write_1 when only EN_write_0 and EN_write_1 are high.
    check_read2_captures_write1_when_en01_only: assert property (
        @(posedge CLK) (EN_write_0 && EN_write_1 && !EN_write_2) |=> (read_2 == $past(write_1))
    );

    // read_2 captures write_0 when only EN_write_0 is high.
    check_read2_captures_write0_when_en0_only: assert property (
        @(posedge CLK) (EN_write_0 && !EN_write_1 && !EN_write_2) |=> (read_2 == $past(write_0))
    );

endmodule