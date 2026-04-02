module mips_shifter_assertions (
    input logic CLK,
    input logic [31:0] Data_in,
    input logic [4:0] Count,
    input logic [1:0] Sel,
    output logic [31:0] Data_out
);

    // ShiftData0 is correctly assigned based on Sel and Count
    shift_data0_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(Data_in) |-> $stable(ShiftData0)
    );

    // ShiftData1 is correctly assigned based on ShiftData0 and Sel and Count
    shift_data1_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(ShiftData0) |-> $stable(ShiftData1)
    );

    // ShiftData2 is correctly assigned based on ShiftData1 and Sel and Count
    shift_data2_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(ShiftData1) |-> $stable(ShiftData2)
    );

    // ShiftData3 is correctly assigned based on ShiftData2 and Sel and Count
    shift_data3_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(ShiftData2) |-> $stable(ShiftData3)
    );

    // Data_out is correctly assigned based on ShiftData3 and Sel and Count
    data_out_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(ShiftData3) |-> $stable(Data_out)
    );

    // HighBit is correctly assigned based on Sel and Data_in
    high_bit_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(Sel) |-> $stable(Data_in) |-> $stable(HighBit)
    );

    // Select is correctly assigned based on Sel and Count
    select_assignment: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(Sel) |-> $stable(Count) |-> $stable(Select)
    );

    // Data_out is correctly assigned based on Data_in, Count, and Sel
    data_out_behavior: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(Data_in) |-> $stable(Count) |-> $stable(Sel) |-> (Data_out == (Sel[1] == 1'b0) ? ((Sel[0] == 1'b0) ? Data_in : (Data_in << Count)) : ((Sel[0] == 1'b0) ? (Data_in >> Count) : (Data_in << Count)))
    );

endmodule