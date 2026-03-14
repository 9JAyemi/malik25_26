module uparc_fwdu_sva (
    input logic [4:0] rs,
    input logic [31:0] rs_data,
    input logic [4:0] rt,
    input logic [31:0] rt_data,
    input logic [4:0] rd_p2,
    input logic [31:0] rd_data_p2,
    input logic pend_mem_load_p2,
    input logic [4:0] rd_p3,
    input logic [31:0] rd_data_p3,
    input logic [31:0] rs_data_p1,
    input logic [31:0] rt_data_p1
);
    // rs forwards from P2 when rs matches rd_p2.
    check_rs_from_p2: assert property (
        @(posedge $global_clock) (rs == rd_p2) |-> (rs_data_p1 == rd_data_p2)
    );

    // rs forwards from P3 when no P2 match and rs matches rd_p3.
    check_rs_from_p3: assert property (
        @(posedge $global_clock) (rs != rd_p2) && (rs == rd_p3) |-> (rs_data_p1 == rd_data_p3)
    );

    // rs takes register file data when no match with P2 or P3.
    check_rs_from_regfile: assert property (
        @(posedge $global_clock) (rs != rd_p2) && (rs != rd_p3) |-> (rs_data_p1 == rs_data)
    );

    // rt forwards from P2 when rt matches rd_p2 and no pending load.
    check_rt_from_p2_when_no_load: assert property (
        @(posedge $global_clock) (rt == rd_p2) && (!pend_mem_load_p2) |-> (rt_data_p1 == rd_data_p2)
    );

    // rt forwards from P3 when P2 path not taken and rt matches rd_p3.
    check_rt_from_p3_when_p2_blocked: assert property (
        @(posedge $global_clock) (rt == rd_p3) && (pend_mem_load_p2 || (rt != rd_p2)) |-> (rt_data_p1 == rd_data_p3)
    );

    // rt takes register file data when P2 path not taken and no P3 match.
    check_rt_from_regfile: assert property (
        @(posedge $global_clock) ((rt != rd_p2) || pend_mem_load_p2) && (rt != rd_p3) |-> (rt_data_p1 == rt_data)
    );

    // When both rt matches and load is pending, P3 has priority.
    check_rt_both_match_load_selects_p3: assert property (
        @(posedge $global_clock) (rt == rd_p2) && (rt == rd_p3) && pend_mem_load_p2 |-> (rt_data_p1 == rd_data_p3)
    );

    // When both rt matches and no load is pending, P2 has priority.
    check_rt_both_match_no_load_selects_p2: assert property (
        @(posedge $global_clock) (rt == rd_p2) && (rt == rd_p3) && !pend_mem_load_p2 |-> (rt_data_p1 == rd_data_p2)
    );
endmodule