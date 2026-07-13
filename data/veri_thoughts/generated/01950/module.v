
module behavioral(out, a, b, e, w);

input a, b, e, w;
output out;

reg out;

always @ (*)
begin
    if (~a & ~b & ~e & ~w)
        out = 1'b1;

    else if (~a & ~b & ~e & w)
        out = 1'b1;

    else if (~a & ~b & e & ~w)
        out = 1'b1;

    else if (~a & ~b & e & w)
        out = 1'b1;

    else if (~a & b & ~e & ~w)
        out = 1'b0;

    else if (~a & b & ~e & w)
        out = 1'b0;

    else if (~a & b & e & ~w)
        out = 1'b0;

    else if (~a & b & e & w)
        out = 1'b0;

    else if (a & ~b & ~e & ~w)
        out = 1'b0;

    else if (a & ~b & ~e & w)
        out = 1'b0;

    else if (a & ~b & e & ~w)
        out = 1'b0;

    else if (a & ~b & e & w)
        out = 1'b0;

    else if (a & b & ~e & ~w)
        out = 1'b0;

    else if (a & b & ~e & w)
        out = 1'b0;

    else if (a & b & e & ~w)
        out = 1'b0;

    else if (a & b & e & w)
        out = 1'b0;

    else
        out = 1'bx;
end

endmodule
