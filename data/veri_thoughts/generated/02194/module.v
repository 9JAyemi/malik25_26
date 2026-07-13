
module three_stage_pipeline(
    input clk,
    input reset,
    input [19:0] b,
    input [19:0] c,
    input [19:0] d,
    output [19:0] q
);

reg [19:0] r_b;
reg [19:0] r_e;
reg [19:0] r_c;
reg [19:0] rr_e;
reg [19:0] rr_b;
reg [19:0] r_qx;

// Create the register (flip-flop) for the initial/1st stage
always@(posedge clk)
begin
    if(reset)
    begin
        r_b<=0;
        r_e<=0;
    end
    else
    begin
        r_e<=r_qx;
        r_b<=d;
    end
end


// Create the register (flip-flop) for the 2nd stage
always@(posedge clk)
begin
    if(reset)
    begin
        r_c<=0;
        rr_e<=0;
        rr_b<=0;
    end
    else
    begin
        r_c<=c;
        rr_e<=r_e;
        rr_b<=r_b;
    end
end


// Create the register (flip-flop) for the 3rd stage
always@(posedge clk)
begin
    if(reset)
    begin
        r_qx<=0;
    end
    else
    begin
        r_qx<=rr_b & r_c & rr_e;
    end
end


// Assign the output q as the bitwise AND of inputs b, c, and d
assign q = r_qx;

endmodule
