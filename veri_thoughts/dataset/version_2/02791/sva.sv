module EHR_6_sva #(
    parameter DATA_SZ   = 1,
    parameter RESET_VAL = 0
) (
    input logic                CLK,
    input logic                RST_N,
    input logic [DATA_SZ-1:0]  read_0,
    input logic [DATA_SZ-1:0]  write_0,
    input logic                EN_write_0,
    input logic [DATA_SZ-1:0]  read_1,
    input logic [DATA_SZ-1:0]  write_1,
    input logic                EN_write_1,
    input logic [DATA_SZ-1:0]  read_2,
    input logic [DATA_SZ-1:0]  write_2,
    input logic                EN_write_2,
    input logic [DATA_SZ-1:0]  read_3,
    input logic [DATA_SZ-1:0]  write_3,
    input logic                EN_write_3,
    input logic [DATA_SZ-1:0]  read_4,
    input logic [DATA_SZ-1:0]  write_4,
    input logic                EN_write_4,
    input logic [DATA_SZ-1:0]  read_5,
    input logic [DATA_SZ-1:0]  write_5,
    input logic                EN_write_5
);
    ///// Reset behavior /////
    // With reset asserted, next-cycle read_0 reflects RESET_VAL.
    reset_drives_read0_next: assert property (
        @(posedge CLK) !RST_N |-> (read_0 == RESET_VAL)
    );

    ///// Combinational read chain (priority mux) /////
    // read_1 selects write_0 when enabled, else read_0.
    chain_read1_mux: assert property (
        @(posedge CLK) disable iff (!RST_N) read_1 == (EN_write_0 ? write_0 : read_0)
    );
    // read_2 selects write_1 when enabled, else read_1.
    chain_read2_mux: assert property (
        @(posedge CLK) disable iff (!RST_N) read_2 == (EN_write_1 ? write_1 : read_1)
    );
    // read_3 selects write_2 when enabled, else read_2.
    chain_read3_mux: assert property (
        @(posedge CLK) disable iff (!RST_N) read_3 == (EN_write_2 ? write_2 : read_2)
    );
    // read_4 selects write_3 when enabled, else read_3.
    chain_read4_mux: assert property (
        @(posedge CLK) disable iff (!RST_N) read_4 == (EN_write_3 ? write_3 : read_3)
    );
    // read_5 selects write_4 when enabled, else read_4.
    chain_read5_mux: assert property (
        @(posedge CLK) disable iff (!RST_N) read_5 == (EN_write_4 ? write_4 : read_4)
    );

    ///// Sequential state update to r (observed via read_0) /////
    // When not in reset in the previous cycle, read_0 updates to (EN_write_5 ? write_5 : read_5) from the previous cycle.
    next_read0_general: assert property (
        @(posedge CLK) disable iff (!RST_N)
            $past(RST_N) |-> (read_0 == $past(EN_write_5 ? write_5 : read_5))
    );
    // With no writes in the previous cycle, read_0 holds its value.
    next_read0_holds_no_writes: assert property (
        @(posedge CLK) disable iff (!RST_N)
            $past(RST_N && !EN_write_0 && !EN_write_1 && !EN_write_2 && !EN_write_3 && !EN_write_4 && !EN_write_5)
            |-> (read_0 == $past(read_0))
    );

    ///// Priority update cases to r (highest to lowest) /////
    // If EN_write_5 was high, next read_0 equals write_5 from the previous cycle.
    next_read0_prio5: assert property (
        @(posedge CLK) disable iff (!RST_N)
            $past(RST_N && EN_write_5) |-> (read_0 == $past(write_5))
    );
    // If only EN_write_4 was the highest active, next read_0 equals write_4.
    next_read0_prio4: assert property (
        @(posedge CLK) disable iff (!RST_N)
            $past(RST_N && !EN_write_5 && EN_write_4) |-> (read_0 == $past(write_4))
    );
    // If only EN_write_3 was the highest active, next read_0 equals write_3.
    next_read0_prio3: assert property (
        @(posedge CLK) disable iff (!RST_N)
            $past(RST_N && !EN_write_5 && !EN_write_4 && EN_write_3) |-> (read_0 == $past(write_3))
    );
    // If only EN_write_2 was the highest active, next read_0 equals write_2.
    next_read0_prio2: assert property (
        @(posedge CLK) disable iff (!RST_N)
            $past(RST_N && !EN_write_5 && !EN_write_4 && !EN_write_3 && EN_write_2) |-> (read_0 == $past(write_2))
    );
    // If only EN_write_1 was the highest active, next read_0 equals write_1.
    next_read0_prio1: assert property (
        @(posedge CLK) disable iff (!RST_N)
            $past(RST_N && !EN_write_5 && !EN_write_4 && !EN_write_3 && !EN_write_2 && EN_write_1)
            |-> (read_0 == $past(write_1))
    );
    // If only EN_write_0 was the highest active, next read_0 equals write_0.
    next_read0_prio0: assert property (
        @(posedge CLK) disable iff (!RST_N)
            $past(RST_N && !EN_write_5 && !EN_write_4 && !EN_write_3 && !EN_write_2 && !EN_write_1 && EN_write_0)
            |-> (read_0 == $past(write_0))
    );
endmodule