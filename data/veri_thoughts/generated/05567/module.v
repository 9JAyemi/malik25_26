module Mflipflop_s (output out, input in, input scanen, input sin, input clock, input reset);
    wire reset_nor;
    assign reset_nor = ~(reset & ~clock);

    dff dff (
        .Q(out),
        .D(in),
        .SM(scanen),
        .SI(sin),
        .CK(clock),
        .R(reset_nor)
    );

endmodule

module dff (output reg Q, input D, input SM, input SI, input CK, input R);
    always @(posedge CK or negedge R)
    begin
        if (!R)
            Q <= 1'b0;
        else if (SM)
            Q <= SI;
        else
            Q <= D;
    end
endmodule