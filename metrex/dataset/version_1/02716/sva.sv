// SVA checker for log2_table. Bind this to the DUT instance.
// Focus: functional equivalence, corner cases, ranges, monotonicity, and coverage.

module log2_table_sva
(
  input logic        clk,
  input logic        trilinear_en,
  input logic [31:0] val,
  input logic [9:0]  log2
);

  // Golden model: exact functional mirror of DUT decision tree
  function automatic [9:0] calc_log2(input logic [31:0] v, input logic tri);
    logic [3:0] int_mm_no;
    logic [5:0] lod_fract;
    logic [10:0] key;
    begin
      key = {|v[31:18], v[17:8]}; // {over_flow, log_in}
      unique casez (key)
        11'b0_10???????_?, 11'b0_011??????_?: begin
          if (tri && v[17]) begin int_mm_no = 4'h9; lod_fract = v[16:11]; end
          else                begin int_mm_no = 4'h8; lod_fract = v[15:10]; end
        end
        11'b0_010??????_?, 11'b0_0011?????_?: begin
          if (tri && v[16]) begin int_mm_no = 4'h8; lod_fract = v[15:10]; end
          else                begin int_mm_no = 4'h7; lod_fract = v[14:9];  end
        end
        11'b0_0010?????_?, 11'b0_00011????_?: begin
          if (tri && v[15]) begin int_mm_no = 4'h7; lod_fract = v[14:9];  end
          else                begin int_mm_no = 4'h6; lod_fract = v[13:8];  end
        end
        11'b0_00010????_?, 11'b0_000011???_?: begin
          if (tri && v[14]) begin int_mm_no = 4'h6; lod_fract = v[13:8];  end
          else                begin int_mm_no = 4'h5; lod_fract = v[12:7];  end
        end
        11'b0_000010???_?, 11'b0_0000011??_?: begin
          if (tri && v[13]) begin int_mm_no = 4'h5; lod_fract = v[12:7];  end
          else                begin int_mm_no = 4'h4; lod_fract = v[11:6];  end
        end
        11'b0_0000010??_?, 11'b0_00000011?_?: begin
          if (tri && v[12]) begin int_mm_no = 4'h4; lod_fract = v[11:6];  end
          else                begin int_mm_no = 4'h3; lod_fract = v[10:5];  end
        end
        11'b0_00000010?_?, 11'b0_000000011_?: begin
          if (tri && v[11]) begin int_mm_no = 4'h3; lod_fract = v[10:5];  end
          else                begin int_mm_no = 4'h2; lod_fract = v[9:4];   end
        end
        11'b0_000000010_?, 11'b0_000000001_1: begin
          if (tri && v[10]) begin int_mm_no = 4'h2; lod_fract = v[9:4];   end
          else                begin int_mm_no = 4'h1; lod_fract = v[8:3];   end
        end
        11'b0_000000001_0, 11'b0_000000000_?: begin
          if (tri && v[9])  begin int_mm_no = 4'h1; lod_fract = v[8:3];   end
          else                begin int_mm_no = 4'h0; lod_fract = v[7:2];   end
        end
        default: begin
          int_mm_no = 4'h9; lod_fract = v[16:11];
        end
      endcase
      return {int_mm_no, lod_fract};
    end
  endfunction

  // Core functional equivalence (one-cycle latency due to flops)
  property p_func_equiv;
    @(posedge clk)
      !$isunknown($past({val,trilinear_en})) |-> (log2 == calc_log2($past(val), $past(trilinear_en)));
  endproperty
  assert property (p_func_equiv);

  // No X/Z on output
  assert property (@(posedge clk) !$isunknown(log2));

  // Integer field range
  assert property (@(posedge clk) (log2[9:6] inside {[0:9]}));

  // Explicit overflow behavior
  assert property (@(posedge clk)
    $past(|val[31:18]) |-> (log2 == {4'h9, $past(val[16:11])})
  );

  // Stability: if inputs stable, output stable
  assert property (@(posedge clk)
    (!$isunknown($past({val,trilinear_en})) && $stable(val) && $stable(trilinear_en)) |-> $stable(log2)
  );

  // Monotonicity: if val increases and tri is stable, output does not decrease
  assert property (@(posedge clk)
    (!$isunknown($past({val,trilinear_en})) && ($past(val) < val) && ($past(trilinear_en)==trilinear_en)) |-> ($past(log2) <= log2)
  );

  // ------------- Coverage -------------

  // Hit all integer outputs 0..9
  genvar i;
  generate
    for (i=0; i<=9; i++) begin : C_INT
      cover property (@(posedge clk) log2[9:6] == i[3:0]);
    end
  endgenerate

  // Overflow covered
  cover property (@(posedge clk) $past(|val[31:18])) ;

  // Exercise both trilinear modes
  cover property (@(posedge clk) $rose(trilinear_en));
  cover property (@(posedge clk) $fell(trilinear_en));

  // Show cases where trilinear changes the integer result for the same val
  cover property (@(posedge clk)
    !$isunknown($past(val)) &&
    (calc_log2($past(val),1'b1)[9:6] != calc_log2($past(val),1'b0)[9:6])
  );

  // And where it does not change it
  cover property (@(posedge clk)
    !$isunknown($past(val)) &&
    (calc_log2($past(val),1'b1)[9:6] == calc_log2($past(val),1'b0)[9:6])
  );

endmodule

// Example bind (edit instance path as needed):
// bind log2_table log2_table_sva u_log2_table_sva (.*);