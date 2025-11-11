// SVA checker for mux4
module mux4_sva #(parameter int WIDTH=32, parameter DISABLED=0)
(
  input  logic                 en,
  input  logic [1:0]           sel,
  input  logic [WIDTH-1:0]     i0, i1, i2, i3,
  input  logic [WIDTH-1:0]     o
);

  // Width-cast disabled value
  localparam logic [WIDTH-1:0] DISABLED_VAL = logic [WIDTH-1:0]'(DISABLED);

  // Combinational functional checks + coverage
  always_comb begin
    // Control signals must be known
    assert (!$isunknown(en))  else $error("mux4_sva: en is X/Z");
    assert (!$isunknown(sel)) else $error("mux4_sva: sel is X/Z");

    if (en) begin
      unique case (sel)
        2'b00: begin
          assert (o === i0) else $error("mux4_sva: o != i0 when sel=00");
          if (!$isunknown(i0)) assert (!$isunknown(o)) else $error("mux4_sva: o X/Z with known i0");
        end
        2'b01: begin
          assert (o === i1) else $error("mux4_sva: o != i1 when sel=01");
          if (!$isunknown(i1)) assert (!$isunknown(o)) else $error("mux4_sva: o X/Z with known i1");
        end
        2'b10: begin
          assert (o === i2) else $error("mux4_sva: o != i2 when sel=10");
          if (!$isunknown(i2)) assert (!$isunknown(o)) else $error("mux4_sva: o X/Z with known i2");
        end
        2'b11: begin
          assert (o === i3) else $error("mux4_sva: o != i3 when sel=11");
          if (!$isunknown(i3)) assert (!$isunknown(o)) else $error("mux4_sva: o X/Z with known i3");
        end
      endcase
    end
    else begin
      assert (o === DISABLED_VAL) else $error("mux4_sva: o != DISABLED_VAL when en==0");
      assert (!$isunknown(o))     else $error("mux4_sva: o X/Z when disabled");
    end

    // Functional coverage
    cover (!en);
    cover (en && sel==2'b00);
    cover (en && sel==2'b01);
    cover (en && sel==2'b10);
    cover (en && sel==2'b11);
  end

endmodule

// Bind to DUT
bind mux4 mux4_sva #(.WIDTH(WIDTH), .DISABLED(DISABLED))
  mux4_sva_i (.en(en), .sel(sel), .i0(i0), .i1(i1), .i2(i2), .i3(i3), .o(o));