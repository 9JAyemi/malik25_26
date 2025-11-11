module SEG7_COUNTER (
    input iCLK,
    input iRST,
    output reg [6:0] oSEG
);
    reg [3:0] count;

    always @(posedge iCLK)
    begin
        if (iRST) // reset counter to 0 when iRST is high
            count <= 0;
        else if (count == 4'd9) // reset counter to 0 when it reaches 9
            count <= 0;
        else // increment counter by 1
            count <= count + 4'd1;
    end

    always @(*)
    begin
        case(count)
            4'd0: oSEG = 7'b1000000; // 0
            4'd1: oSEG = 7'b1111001; // 1
            4'd2: oSEG = 7'b0100100; // 2
            4'd3: oSEG = 7'b0110000; // 3
            4'd4: oSEG = 7'b0011001; // 4
            4'd5: oSEG = 7'b0010010; // 5
            4'd6: oSEG = 7'b0000010; // 6
            4'd7: oSEG = 7'b1111000; // 7
            4'd8: oSEG = 7'b0000000; // 8
            4'd9: oSEG = 7'b0010000; // 9
            default: oSEG = 7'b1111111; // display nothing
        endcase
    end
endmodule