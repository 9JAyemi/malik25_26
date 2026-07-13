module mux4to1 (
    output reg [7:0] out,
    input [7:0] in0,
    input [7:0] in1,
    input [7:0] in2,
    input [7:0] in3,
    input sel0,
    input sel1
);

    // Local signals
    reg [7:0] selected;

    // Select the input based on the select lines
    always @*
    begin
        case ({sel1, sel0})
            2'b00: selected = in0;
            2'b01: selected = in1;
            2'b10: selected = in2;
            2'b11: selected = in3;
        endcase
    end

    // Assign the selected input to the output
    always @*
    begin
        out = selected;
    end

endmodule