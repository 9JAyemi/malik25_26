module SwapUnit_sva (
    input logic [4:0] rs,
    input logic [4:0] rt,
    input logic [4:0] rd,
    input logic EXMEMregWrite,
    input logic [4:0] EXMEMregisterRd,
    input logic [4:0] MEMWBregisterRd,
    input logic MEMWBregWrite,
    input logic [1:0] forwardB,
    input logic [1:0] forwardA,
    input logic rst
);
    ///// Reset behavior /////
    // On rst assertion, both forwardA and forwardB drive 0.
    reset_outputs_zero: assert property (
        @(posedge rst) (forwardA == 2'b00) && (forwardB == 2'b00)
    );

    ///// forwardA selection logic /////
    // If EXMEM matches rs and is valid, forwardA selects 2'b10.
    check_forwardA_from_EXMEM: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        (EXMEMregWrite && (EXMEMregisterRd != 5'd0) && (EXMEMregisterRd == rs)) |-> (forwardA == 2'b10)
    );
    // If MEMWB matches rs and EXMEM does not, forwardA selects 2'b01.
    check_forwardA_from_MEMWB_no_EXMEM: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        (MEMWBregWrite && (MEMWBregisterRd != 5'd0) && (MEMWBregisterRd == rs) &&
         !(EXMEMregWrite && (EXMEMregisterRd != 5'd0) && (EXMEMregisterRd == rs))) |-> (forwardA == 2'b01)
    );
    // If neither EXMEM nor MEMWB matches rs, forwardA is 2'b00.
    check_forwardA_default_zero: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        !(EXMEMregWrite && (EXMEMregisterRd != 5'd0) && (EXMEMregisterRd == rs)) &&
        !(MEMWBregWrite && (MEMWBregisterRd != 5'd0) && (MEMWBregisterRd == rs)) |-> (forwardA == 2'b00)
    );
    // When both EXMEM and MEMWB match rs, EXMEM has priority (2'b10).
    check_forwardA_EXMEM_priority: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        (EXMEMregWrite && (EXMEMregisterRd != 5'd0) && (EXMEMregisterRd == rs) &&
         MEMWBregWrite && (MEMWBregisterRd != 5'd0) && (MEMWBregisterRd == rs)) |-> (forwardA == 2'b10)
    );
    // forwardA only takes 00, 01, or 10 when not in reset.
    check_forwardA_code_space: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        1'b1 |-> (forwardA inside {2'b00, 2'b01, 2'b10})
    );

    ///// forwardB selection logic /////
    // If EXMEM matches rt and is valid, forwardB selects 2'b10.
    check_forwardB_from_EXMEM: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        (EXMEMregWrite && (EXMEMregisterRd != 5'd0) && (EXMEMregisterRd == rt)) |-> (forwardB == 2'b10)
    );
    // If MEMWB matches rt and EXMEM does not, forwardB selects 2'b01.
    check_forwardB_from_MEMWB_no_EXMEM: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        (MEMWBregWrite && (MEMWBregisterRd != 5'd0) && (MEMWBregisterRd == rt) &&
         !(EXMEMregWrite && (EXMEMregisterRd != 5'd0) && (EXMEMregisterRd == rt))) |-> (forwardB == 2'b01)
    );
    // If neither EXMEM nor MEMWB matches rt, forwardB is 2'b00.
    check_forwardB_default_zero: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        !(EXMEMregWrite && (EXMEMregisterRd != 5'd0) && (EXMEMregisterRd == rt)) &&
        !(MEMWBregWrite && (MEMWBregisterRd != 5'd0) && (MEMWBregisterRd == rt)) |-> (forwardB == 2'b00)
    );
    // When both EXMEM and MEMWB match rt, EXMEM has priority (2'b10).
    check_forwardB_EXMEM_priority: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        (EXMEMregWrite && (EXMEMregisterRd != 5'd0) && (EXMEMregisterRd == rt) &&
         MEMWBregWrite && (MEMWBregisterRd != 5'd0) && (MEMWBregisterRd == rt)) |-> (forwardB == 2'b10)
    );
    // forwardB only takes 00, 01, or 10 when not in reset.
    check_forwardB_code_space: assert property (
        @(posedge EXMEMregWrite or posedge MEMWBregWrite or posedge rst)
        disable iff (rst)
        1'b1 |-> (forwardB inside {2'b00, 2'b01, 2'b10})
    );

endmodule