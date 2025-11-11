
module majority_gate(
    input a, 
    input b,
    input c,
    input reset,
    output wire out_assign,
    output reg out_alwaysblock
);

    // Majority gate using assign statements
    assign out_assign = (a & b) | (a & c) | (b & c);
    
    // Majority gate using a combinational always block
    always @* begin
        if(reset == 1'b1)
             out_alwaysblock = 1'b0;
        else begin
           case ({a, b, c}) 
             3'b111: out_alwaysblock = 1'b1;
             3'b110: out_alwaysblock = 1'b1;
             3'b101: out_alwaysblock = 1'b1;
             3'b011: out_alwaysblock = 1'b1;
             default: out_alwaysblock = 1'b0;
           endcase
       end
    end

endmodule