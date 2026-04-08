
module v3676a0 (
    input vcbab45,
    output reg v0e28cb
);
    always @(*) begin
        v0e28cb <= vcbab45;
    end
endmodule
module vba518e (
    input vcbab45,
    input v0e28cb,
    input v3ca442
);
    wire w0;
    assign w0 = vcbab45 & v3ca442;
    v3676a0 v3676a0_inst (
        .vcbab45(w0),
        .v0e28cb(v0e28cb)
    );
endmodule
module v053dc2 (
    input vf54559,
    input va4102a,
    output reg ve8318d
);
    always @(*) begin
        ve8318d <= vf54559 | va4102a;
    end
endmodule
module v2be0f8 #(
    parameter vbd3217 = 0
) (
    input vd53b77,
    input v27dec4,
    input vf354ee,
    output reg v4642b6
);
    wire w0, w1, w2, w3;
    assign w0 = vd53b77;
    assign w2 = v27dec4;
    assign w3 = vf354ee;
    vba518e vba518e_inst (
        .vcbab45(w0),
        .v0e28cb(w1),
        .v3ca442(w3)
    );
    v053dc2 v053dc2_inst (
        .vf54559(w0),
        .va4102a(w2),
        .ve8318d(v4642b6)
    );
endmodule