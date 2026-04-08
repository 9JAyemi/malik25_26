module ByteMuxOct_sva (
    input logic clk,
    input logic [7:0] A_i,
    input logic [7:0] B_i,
    input logic [7:0] C_i,
    input logic [7:0] D_i,
    input logic [7:0] E_i,
    input logic [7:0] F_i,
    input logic [7:0] G_i,
    input logic [7:0] H_i,
    input logic SAB_i,
    input logic SC_i,
    input logic SD_i,
    input logic SE_i,
    input logic SF_i,
    input logic SG_i,
    input logic SH_i,
    input logic [7:0] Y_o
);

    // Output matches the full nested mux expression.
    check_full_mux_function: assert property (
        @(posedge clk)
        Y_o == (SH_i ? H_i :
                (SG_i ? G_i :
                 (SF_i ? F_i :
                  (SE_i ? E_i :
                   (SD_i ? D_i :
                    (SC_i ? C_i :
                     (SAB_i ? B_i : A_i)))))))
    );

    // H is selected when the top-level select is asserted.
    check_select_h: assert property (
        @(posedge clk)
        SH_i |-> (Y_o == H_i)
    );

    // G is selected when SH_i is low and SG_i is high.
    check_select_g: assert property (
        @(posedge clk)
        (!SH_i && SG_i) |-> (Y_o == G_i)
    );

    // F is selected when higher-priority selects are low and SF_i is high.
    check_select_f: assert property (
        @(posedge clk)
        (!SH_i && !SG_i && SF_i) |-> (Y_o == F_i)
    );

    // E is selected when higher-priority selects are low and SE_i is high.
    check_select_e: assert property (
        @(posedge clk)
        (!SH_i && !SG_i && !SF_i && SE_i) |-> (Y_o == E_i)
    );

    // D is selected when higher-priority selects are low and SD_i is high.
    check_select_d: assert property (
        @(posedge clk)
        (!SH_i && !SG_i && !SF_i && !SE_i && SD_i) |-> (Y_o == D_i)
    );

    // C is selected when higher-priority selects are low and SC_i is high.
    check_select_c: assert property (
        @(posedge clk)
        (!SH_i && !SG_i && !SF_i && !SE_i && !SD_i && SC_i) |-> (Y_o == C_i)
    );

    // B is selected when only the lowest-level select is asserted.
    check_select_b: assert property (
        @(posedge clk)
        (!SH_i && !SG_i && !SF_i && !SE_i && !SD_i && !SC_i && SAB_i) |-> (Y_o == B_i)
    );

    // A is selected when all select inputs are deasserted.
    check_select_a: assert property (
        @(posedge clk)
        (!SH_i && !SG_i && !SF_i && !SE_i && !SD_i && !SC_i && !SAB_i) |-> (Y_o == A_i)
    );

endmodule