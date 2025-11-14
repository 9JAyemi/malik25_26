
module Serial_in_parallel_out_enable_behavior(

    input Clk, ShiftIn, reset, ShiftEn,
    output wire ShiftOut,
    output wire [3:0] ParallelOut
    );

    reg [15:0] ShiftReg;
    reg [3:0] ParallelReg;

    always @(posedge Clk) begin
        if (reset) begin
            ShiftReg <= 16'h0000;
        end
        else if (ShiftEn) begin
            ShiftReg <= {ShiftReg[14:0], ShiftIn};
        end
    end

    always @(posedge Clk) begin
        if (reset) begin
            ParallelReg <= 4'b0000;
        end
        else if (ShiftEn) begin
            ParallelReg[0] <= ShiftReg[3:0];
            ParallelReg[1] <= ShiftReg[7:4];
            ParallelReg[2] <= ShiftReg[11:8];
            ParallelReg[3] <= ShiftReg[15:12];
        end
    end

    assign ShiftOut = ShiftReg[15];
    assign ParallelOut = ParallelReg;

endmodule
