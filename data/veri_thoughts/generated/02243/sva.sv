module IF_sva (
    input logic clk,
    input logic rst,
    input logic flush,
    input logic [31:0] PC_In,
    input logic [2:0] PCSrc,
    input logic PCWrite,
    input logic Branch,
    input logic [31:0] ConBA,
    input logic [31:0] DataBusA,
    input logic [25:0] JT,
    input logic [31:0] PC_Out
);
    // Clock: clk; Reset: rst (active-high async). Logic: sequential.

    ///// Reset behavior /////
    // While reset is asserted, PC_Out is 0.
    reset_drives_zero: assert property (
        @(posedge clk) rst |-> (PC_Out == 32'h0000_0000)
    );

    ///// Hold behavior /////
    // When not flushing and PCWrite is LOW, PC_Out holds its value.
    hold_when_no_write: assert property (
        @(posedge clk) disable iff (rst)
            (!flush && !PCWrite) |=> (PC_Out == $past(PC_Out))
    );

    ///// Flush behavior /////
    // When flush is asserted, next PC_Out keeps old MSB and clears lower 31 bits.
    flush_clears_lower31: assert property (
        @(posedge clk) disable iff (rst)
            flush |=> (PC_Out == { $past(PC_Out[31]), {31{1'b0}} })
    );

    ///// Write/Branch/PCSrc behavior /////
    // On PCWrite with Branch, next PC_Out equals ConBA.
    branch_updates_to_ConBA: assert property (
        @(posedge clk) disable iff (rst)
            (!flush && PCWrite && Branch) |=> (PC_Out == $past(ConBA))
    );

    // On PCWrite without Branch and PCSrc=0 or 1, next PC_Out equals PC_In+4.
    pcs01_inc4: assert property (
        @(posedge clk) disable iff (rst)
            (!flush && PCWrite && !Branch && (PCSrc inside {3'h0,3'h1})) |=> (PC_Out == ($past(PC_In) + 32'h4))
    );

    // On PCWrite without Branch and PCSrc=2, next PC_Out equals {PC_In[31:28], JT, 2'b0}.
    pcs2_jump_address: assert property (
        @(posedge clk) disable iff (rst)
            (!flush && PCWrite && !Branch && (PCSrc == 3'h2)) |=> (PC_Out == { $past(PC_In[31:28]), $past(JT), 2'b0 })
    );

    // On PCWrite without Branch and PCSrc=2, LSBs of next PC_Out are 0.
    pcs2_lsb_zero: assert property (
        @(posedge clk) disable iff (rst)
            (!flush && PCWrite && !Branch && (PCSrc == 3'h2)) |=> (PC_Out[1:0] == 2'b00)
    );

    // On PCWrite without Branch and PCSrc=3, next PC_Out equals DataBusA.
    pcs3_load_from_DataBusA: assert property (
        @(posedge clk) disable iff (rst)
            (!flush && PCWrite && !Branch && (PCSrc == 3'h3)) |=> (PC_Out == $past(DataBusA))
    );

    // On PCWrite without Branch and PCSrc=4, next PC_Out equals 0x80000004.
    pcs4_const_8000_0004: assert property (
        @(posedge clk) disable iff (rst)
            (!flush && PCWrite && !Branch && (PCSrc == 3'h4)) |=> (PC_Out == 32'h8000_0004)
    );

    // On PCWrite without Branch and PCSrc=5, next PC_Out equals 0x80000008.
    pcs5_const_8000_0008: assert property (
        @(posedge clk) disable iff (rst)
            (!flush && PCWrite && !Branch && (PCSrc == 3'h5)) |=> (PC_Out == 32'h8000_0008)
    );

    // On PCWrite without Branch and PCSrc not in 0..5 (i.e., 6 or 7), next PC_Out equals 0x80000008.
    default_const_8000_0008: assert property (
        @(posedge clk) disable iff (rst)
            (!flush && PCWrite && !Branch && !(PCSrc inside {3'h0,3'h1,3'h2,3'h3,3'h4,3'h5})) |=> (PC_Out == 32'h8000_0008)
    );

endmodule