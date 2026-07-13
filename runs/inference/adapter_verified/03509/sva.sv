module EHRU_3_sva (
    input logic CLK,
    input logic [0:0] read_0,
    input logic [0:0] write_0,
    input logic EN_write_0,
    input logic [0:0] read_1,
    input logic [0:0] write_1,
    input logic EN_write_1,
    input logic [0:0] read_2,
    input logic [0:0] write_2,
    input logic EN_write_2
);

// read_0 reflects the previous cycle's write_0 when EN_write_0 is high.
    check_read0_from_prev_write0_when_en: assert property (
        @(posedge CLK) EN_write_0 |=> (read_0 == $past(write_0))
    );

// read_0 holds its previous value when EN_write_0 is low.
    check_read0_holds_when_en0: assert property (
        @(posedge CLK) !EN_write_0 |=> (read_0 == $past(read_0))
    );

// read_1 reflects the previous cycle's write_1 when EN_write_1 is high.
    check_read1_from_prev_write1_when_en: assert property (
        @(posedge CLK) EN_write_1 |=> (read_1 == $past(write_1))
    );

// read_1 holds its previous value when EN_write_1 is low.
    check_read1_holds_when_en0: assert property (
        @(posedge CLK) !EN_write_1 |=> (read_1 == $past(read_1))
    );

// read_2 reflects the previous cycle's write_2 when EN_write_2 is high.
    check_read2_from_prev_write2_when_en: assert property (
        @(posedge CLK) EN_write_2 |=> (read_2 == $past(write_2))
    );

// read_2 holds its previous value when EN_write_2 is low.
    check_read2_holds_when_en0: assert property (
        @(posedge CLK) !EN_write_2 |=> (read_2 == $past(read_2))
    );

endmodule
