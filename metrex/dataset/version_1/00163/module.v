
module quadrature_decoder(
    CLOCK, 
    RESET, 
    A, 
    B, 
    COUNT_ENABLE, 
    DIRECTION, 
    SPEED
);

    input CLOCK, RESET, A, B;
    output COUNT_ENABLE;
    output DIRECTION;
    output [3:0] SPEED;
    reg COUNT_ENABLE;
    reg DIRECTION;
    reg [3:0] SPEED;

    reg [2:0] A_delayed;
    reg [2:0] B_delayed;
    reg [31:0] total;
    wire count_enable;
    wire count_direction;
    
    always @(posedge CLOCK or posedge RESET) begin 
        if (RESET) begin 
            A_delayed <= 0;
            B_delayed <= 0;
        end else begin
            A_delayed <= {A_delayed[1:0], A};
            B_delayed <= {B_delayed[1:0], B};
        end
    end
    
    assign count_enable = A_delayed[1] ^ A_delayed[2] ^ B_delayed[1] ^ B_delayed[2];
    assign count_direction = A_delayed[1] ^ B_delayed[2];
    
    always @(posedge CLOCK or posedge RESET) begin
        if (RESET) begin 
            total <= 0;
        end 
        else if (count_enable) begin
            // only want a final count between 0 & 27 (x4 for the clicks)
            if (count_direction) begin 
                if (total < 109) begin 
                    total <= total+1; 
                end
            end
            else begin 
                if (total > 0) begin 
                    total <= total-1;
                end
            end
        end
    end
    
    always @(posedge CLOCK or posedge RESET) begin
        if (RESET) begin
            COUNT_ENABLE <= 0;
            DIRECTION <= 0;
            SPEED <= 0;
        end
        else begin
            COUNT_ENABLE <= count_enable & ~COUNT_ENABLE;
            DIRECTION <= count_direction & ~DIRECTION;
            SPEED <= total[5:2];
        end
    end
endmodule