
module mux4 (
    input A0,
    input A1,
    input A2,
    input A3,
    input S0,
    input S1,
    output X,
    input VPB,
    input VPWR,
    input VGND,
    input VNB
);

reg [3:0] inputs;
reg [1:0] select;

always @(posedge S0) begin
    select[0] <= S0;
end

always @(posedge S1) begin
    select[1] <= S1;
end

always @ (select, A0, A1, A2, A3) begin
    case (select)
        2'b00: inputs = {A0, 1'b0, 1'b0, 1'b0};
        2'b01: inputs = {1'b0, A1, 1'b0, 1'b0};
        2'b10: inputs = {1'b0, 1'b0, A2, 1'b0};
        2'b11: inputs = {1'b0, 1'b0, 1'b0, A3};
    endcase
end

assign X = inputs[3] | inputs[2] | inputs[1] | inputs[0];

endmodule