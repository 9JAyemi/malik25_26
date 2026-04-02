module EHRU_3_assertions (
    input logic CLK,
    input logic RESETn,
    input logic [DATA_SZ-1:0] read_0,
    input logic [DATA_SZ-1:0] write_0,
    input logic EN_write_0,
    input logic [DATA_SZ-1:0] read_1,
    input logic [DATA_SZ-1:0] write_1,
    input logic EN_write_1,
    input logic [DATA_SZ-1:0] read_2,
    input logic [DATA_SZ-1:0] write_2,
    input logic EN_write_2
);
    parameter            DATA_SZ = 1;
    parameter            RESET_VAL = 0;

    reg    [DATA_SZ-1:0] r;
    wire   [DATA_SZ-1:0] wire_0;
    wire   [DATA_SZ-1:0] wire_1;
    wire   [DATA_SZ-1:0] wire_2;
    wire   [DATA_SZ-1:0] wire_3;

    assign wire_0 = r;
    assign wire_1 = EN_write_0 ? write_0 : wire_0;
    assign wire_2 = EN_write_1 ? write_1 : wire_1;
    assign wire_3 = EN_write_2 ? write_2 : wire_2;

    assign read_0 = wire_0;
    assign read_1 = wire_1;
    assign read_2 = wire_2;

    always @(posedge CLK) begin
        r <= wire_3;
    end

    ///// Register update /////
    // Register r should update to wire_3 on every positive edge of CLK.
    reg_update: assert property (
        @(posedge CLK) disable iff (!RESETn) r == wire_3
    );

    ///// Read values /////
    // read_0 should always be equal to wire_0.
    read_0_check: assert property (
        @(posedge CLK) disable iff (!RESETn) read_0 == wire_0
    );
    // read_1 should always be equal to wire_1.
    read_1_check: assert property (
        @(posedge CLK) disable iff (!RESETn) read_1 == wire_1
    );
    // read_2 should always be equal to wire_2.
    read_2_check: assert property (
        @(posedge CLK) disable iff (!RESETn) read_2 == wire_2
    );

    ///// Write enable logic /////
    // wire_1 should be equal to write_0 when EN_write_0 is high.
    write_0_enable: assert property (
        @(posedge CLK) disable iff (!RESETn) (EN_write_0 == 1'b1) |-> wire_1 == write_0
    );
    // wire_2 should be equal to write_1 when EN_write_1 is high.
    write_1_enable: assert property (
        @(posedge CLK) disable iff (!RESETn) (EN_write_1 == 1'b1) |-> wire_2 == write_1
    );
    // wire_3 should be equal to write_2 when EN_write_2 is high.
    write_2_enable: assert property (
        @(posedge CLK) disable iff (!RESETn) (EN_write_2 == 1'b1) |-> wire_3 == write_2
    );

    ///// Reset behavior /////
    // At reset assertion, all outputs should be equal to RESET_VAL.
    reset_check: assert property (
        @(posedge CLK) !RESETn |-> (read_0 == RESET_VAL) && (read_1 == RESET_VAL) && (read_2 == RESET_VAL)
    );
endmodule