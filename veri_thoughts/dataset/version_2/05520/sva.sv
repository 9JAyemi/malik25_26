module losd_store_pipe_arbiter_sva(
    input logic clk,
    input logic oLDST_REQ,
    input logic iLDST_BUSY,
    input logic [1:0] oLDST_ORDER,
    input logic [3:0] oLDST_MASK,
    input logic oLDST_RW,
    input logic [13:0] oLDST_TID,
    input logic [1:0] oLDST_MMUMOD,
    input logic [31:0] oLDST_PDT,
    input logic [31:0] oLDST_ADDR,
    input logic [31:0] oLDST_DATA,
    input logic iLDST_VALID,
    input logic iLDST_PAGEFAULT,
    input logic [13:0] iLDST_MMU_FLAGS,
    input logic [31:0] iLDST_DATA,
    input logic iUSE_SEL,
    input logic iEXE_REQ,
    input logic oEXE_BUSY,
    input logic [1:0] iEXE_ORDER,
    input logic [3:0] iEXE_MASK,
    input logic iEXE_RW,
    input logic [13:0] iEXE_TID,
    input logic [1:0] iEXE_MMUMOD,
    input logic [31:0] iEXE_PDT,
    input logic [31:0] iEXE_ADDR,
    input logic [31:0] iEXE_DATA,
    input logic oEXE_REQ,
    input logic oEXE_PAGEFAULT,
    input logic [13:0] oEXE_MMU_FLAGS,
    input logic [31:0] oEXE_DATA,
    input logic iEXCEPT_REQ,
    input logic oEXCEPT_BUSY,
    input logic [1:0] iEXCEPT_ORDER,
    input logic iEXCEPT_RW,
    input logic [13:0] iEXCEPT_TID,
    input logic [1:0] iEXCEPT_MMUMOD,
    input logic [31:0] iEXCEPT_PDT,
    input logic [31:0] iEXCEPT_ADDR,
    input logic [31:0] iEXCEPT_DATA,
    input logic oEXCEPT_REQ,
    input logic [31:0] oEXCEPT_DATA
);

    // oLDST_REQ selects the request source by iUSE_SEL.
    check_ldst_req_mux: assert property (
        @(posedge clk) disable iff (1'b0)
        (oLDST_REQ == (iUSE_SEL ? iEXCEPT_REQ : iEXE_REQ))
    );

    // oLDST_ORDER selects exception or execution order by iUSE_SEL.
    check_ldst_order_mux: assert property (
        @(posedge clk) disable iff (1'b0)
        (oLDST_ORDER == (iUSE_SEL ? iEXCEPT_ORDER : iEXE_ORDER))
    );

    // oLDST_MASK is fixed to 4'hf for exception traffic, else iEXE_MASK.
    check_ldst_mask_mux: assert property (
        @(posedge clk) disable iff (1'b0)
        (oLDST_MASK == (iUSE_SEL ? 4'hf : iEXE_MASK))
    );

    // oLDST_RW selects the read/write control by iUSE_SEL.
    check_ldst_rw_mux: assert property (
        @(posedge clk) disable iff (1'b0)
        (oLDST_RW == (iUSE_SEL ? iEXCEPT_RW : iEXE_RW))
    );

    // oLDST_TID selects the transaction ID by iUSE_SEL.
    check_ldst_tid_mux: assert property (
        @(posedge clk) disable iff (1'b0)
        (oLDST_TID == (iUSE_SEL ? iEXCEPT_TID : iEXE_TID))
    );

    // oLDST_MMUMOD selects the MMU mode by iUSE_SEL.
    check_ldst_mmumod_mux: assert property (
        @(posedge clk) disable iff (1'b0)
        (oLDST_MMUMOD == (iUSE_SEL ? iEXCEPT_MMUMOD : iEXE_MMUMOD))
    );

    // oLDST_PDT selects the PDT value by iUSE_SEL.
    check_ldst_pdt_mux: assert property (
        @(posedge clk) disable iff (1'b0)
        (oLDST_PDT == (iUSE_SEL ? iEXCEPT_PDT : iEXE_PDT))
    );

    // oLDST_ADDR selects the address by iUSE_SEL.
    check_ldst_addr_mux: assert property (
        @(posedge clk) disable iff (1'b0)
        (oLDST_ADDR == (iUSE_SEL ? iEXCEPT_ADDR : iEXE_ADDR))
    );

    // oLDST_DATA selects the write data by iUSE_SEL.
    check_ldst_data_mux: assert property (
        @(posedge clk) disable iff (1'b0)
        (oLDST_DATA == (iUSE_SEL ? iEXCEPT_DATA : iEXE_DATA))
    );

    // Exception busy mirrors iLDST_BUSY only when exception is selected.
    check_except_busy_routing: assert property (
        @(posedge clk) disable iff (1'b0)
        (oEXCEPT_BUSY == (iUSE_SEL ? iLDST_BUSY : 1'b1))
    );

    // Exception request is valid only when exception is selected.
    check_except_req_routing: assert property (
        @(posedge clk) disable iff (1'b0)
        (oEXCEPT_REQ == (iUSE_SEL ? iLDST_VALID : 1'b0))
    );

    // Exception data always forwards iLDST_DATA.
    check_except_data_forward: assert property (
        @(posedge clk) disable iff (1'b0)
        (oEXCEPT_DATA == iLDST_DATA)
    );

    // Execution busy mirrors iLDST_BUSY only when execution is selected.
    check_exe_busy_routing: assert property (
        @(posedge clk) disable iff (1'b0)
        (oEXE_BUSY == (iUSE_SEL ? 1'b1 : iLDST_BUSY))
    );

    // Execution request is valid only when execution is selected.
    check_exe_req_routing: assert property (
        @(posedge clk) disable iff (1'b0)
        (oEXE_REQ == (iUSE_SEL ? 1'b0 : iLDST_VALID))
    );

    // Execution pagefault always forwards iLDST_PAGEFAULT.
    check_exe_pagefault_forward: assert property (
        @(posedge clk) disable iff (1'b0)
        (oEXE_PAGEFAULT == iLDST_PAGEFAULT)
    );

    // Execution MMU flags always forward iLDST_MMU_FLAGS.
    check_exe_mmu_flags_forward: assert property (
        @(posedge clk) disable iff (1'b0)
        (oEXE_MMU_FLAGS == iLDST_MMU_FLAGS)
    );

    // Execution data always forwards iLDST_DATA.
    check_exe_data_forward: assert property (
        @(posedge clk) disable iff (1'b0)
        (oEXE_DATA == iLDST_DATA)
    );

endmodule