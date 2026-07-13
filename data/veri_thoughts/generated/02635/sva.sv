module EHRU_4_sva #(
    parameter DATA_SZ = 1
) (
    input  logic               CLK,
    input  logic [DATA_SZ-1:0] read_0,
    input  logic [DATA_SZ-1:0] write_0,
    input  logic               EN_write_0,
    input  logic [DATA_SZ-1:0] read_1,
    input  logic [DATA_SZ-1:0] write_1,
    input  logic               EN_write_1,
    input  logic [DATA_SZ-1:0] read_2,
    input  logic [DATA_SZ-1:0] write_2,
    input  logic               EN_write_2,
    input  logic [DATA_SZ-1:0] read_3,
    input  logic [DATA_SZ-1:0] write_3,
    input  logic               EN_write_3
);

    ///// Combinational forwarding on read ports /////
    // read_1 forwards write_0 in-cycle, else passes read_0.
    check_read1_forward_select: assert property (
        @(posedge CLK) read_1 == (EN_write_0 ? write_0 : read_0)
    );

    // read_2 forwards write_1 in-cycle, else passes read_1.
    check_read2_forward_select: assert property (
        @(posedge CLK) read_2 == (EN_write_1 ? write_1 : read_1)
    );

    // read_3 forwards write_2 in-cycle, else passes read_2.
    check_read3_forward_select: assert property (
        @(posedge CLK) read_3 == (EN_write_2 ? write_2 : read_2)
    );

    // read_3 full chain equals write_2/1/0 or read_0 per enable priority.
    check_read3_full_chain: assert property (
        @(posedge CLK) read_3 == (EN_write_2 ? write_2 : (EN_write_1 ? write_1 : (EN_write_0 ? write_0 : read_0)))
    );

    // If EN_write_0 is high, read_1 must equal write_0 in the same cycle.
    check_read1_when_en0: assert property (
        @(posedge CLK) EN_write_0 |-> (read_1 == write_0)
    );

    // If EN_write_1 is high, read_2 must equal write_1 in the same cycle.
    check_read2_when_en1: assert property (
        @(posedge CLK) EN_write_1 |-> (read_2 == write_1)
    );

    // If EN_write_2 is high, read_3 must equal write_2 in the same cycle.
    check_read3_when_en2: assert property (
        @(posedge CLK) EN_write_2 |-> (read_3 == write_2)
    );

    ///// Sequential register update semantics via read_0 (mirror of r) /////
    // If EN_write_3, next read_0 equals write_3 (highest priority).
    check_write3_priority_nextval: assert property (
        @(posedge CLK) EN_write_3 |=> (read_0 == $past(write_3))
    );

    // If !EN_write_3 && EN_write_2, next read_0 equals write_2.
    check_write2_priority_nextval: assert property (
        @(posedge CLK) (!EN_write_3 && EN_write_2) |=> (read_0 == $past(write_2))
    );

    // If !EN_write_3 && !EN_write_2 && EN_write_1, next read_0 equals write_1.
    check_write1_priority_nextval: assert property (
        @(posedge CLK) (!EN_write_3 && !EN_write_2 && EN_write_1) |=> (read_0 == $past(write_1))
    );

    // If only EN_write_0, next read_0 equals write_0.
    check_write0_priority_nextval: assert property (
        @(posedge CLK) (!EN_write_3 && !EN_write_2 && !EN_write_1 && EN_write_0) |=> (read_0 == $past(write_0))
    );

    // If no write enables, next read_0 holds its previous value.
    check_hold_when_no_write: assert property (
        @(posedge CLK) (!EN_write_3 && !EN_write_2 && !EN_write_1 && !EN_write_0) |=> (read_0 == $past(read_0))
    );

endmodule