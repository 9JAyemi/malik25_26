
module or1200_mem2reg(
    input [1:0] addr,
    input [3:0] lsu_op,
    input [31:0] memdata,
    output [31:0] regdata
);

// Logic to convert memory data to register data based on LSU operation
assign regdata = (lsu_op == 4'b0010) ? {{24{memdata[7]}}, memdata[7:0]} :
                (lsu_op == 4'b0011) ? {{16{memdata[15]}}, memdata[15:0]} :
                (lsu_op == 4'b0100) ? {{8{memdata[31]}}, memdata[31:0]} :
                memdata;

endmodule
