
module t2(
    input [1:0] clks,
    input c0,
    input c1,
    input check,
    output reg o_check
);

    reg [1:0] state;
    parameter S0 = 2'b00, S1 = 2'b01, S2 = 2'b10, S3 = 2'b11;
    
    always @(posedge clks[0]) begin
        case(state)
            S0: begin
                if(c0 && !c1)
                    state <= S1;
                else if(!c0 && c1)
                    state <= S2;
            end
            S1: begin
                if(c0 && !c1)
                    state <= S3;
                else if(!c0 && !c1)
                    state <= S0;
            end
            S2: begin
                if(!c0 && c1)
                    state <= S3;
                else if(c0 && !c1)
                    state <= S0;
            end
            S3: begin
                if(!c0 && !c1)
                    state <= S2;
                else if(c0 && c1)
                    state <= S1;
            end
        endcase
    end
    
    always @(posedge clks[1]) begin
        if(state == S3 && check)
            o_check <= 1;
        else
            o_check <= 0;
    end
    
    initial state <= S0;
    
endmodule