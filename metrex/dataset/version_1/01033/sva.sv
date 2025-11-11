// SVA package bound into the DUT to check functionality and provide concise coverage
module four_bit_alu_sva;
  // This module is bound inside four_bit_alu and has hierarchical visibility to its signals

  // Functional correctness and flag checks (guard against X on inputs)
  always @* begin
    if (!$isunknown({ctl,a,b})) begin
      unique case (ctl)
        4'b0000: begin // ADD
          assert (out == (a + b)) else $error("ADD mismatch a=%0h b=%0h out=%0h", a,b,out);
          assert (ovf == ((a[3]==b[3]) && (out[3]!=a[3])))
            else $error("ADD ovf wrong a=%0h b=%0h out=%0h ovf=%0b", a,b,out,ovf);
        end
        4'b0001: begin // SUB
          assert (out == (a - b)) else $error("SUB mismatch a=%0h b=%0h out=%0h", a,b,out);
          // Signed overflow rule for subtraction
          assert (ovf == ((a[3]!=b[3]) && (out[3]!=a[3])))
            else $error("SUB ovf wrong a=%0h b=%0h out=%0h ovf=%0b", a,b,out,ovf);
        end
        4'b0010: begin // AND
          assert (out == (a & b)) else $error("AND mismatch a=%0h b=%0h out=%0h", a,b,out);
          assert (ovf == 1'b0) else $error("ovf must be 0 on AND");
        end
        4'b0011: begin // OR
          assert (out == (a | b)) else $error("OR mismatch a=%0h b=%0h out=%0h", a,b,out);
          assert (ovf == 1'b0) else $error("ovf must be 0 on OR");
        end
        4'b0100: begin // XOR
          assert (out == (a ^ b)) else $error("XOR mismatch a=%0h b=%0h out=%0h", a,b,out);
          assert (ovf == 1'b0) else $error("ovf must be 0 on XOR");
        end
        4'b0101: begin // NOT
          assert (out == (~a)) else $error("NOT mismatch a=%0h out=%0h", a,out);
          assert (ovf == 1'b0) else $error("ovf must be 0 on NOT");
        end
        4'b0110: begin // SHL
          assert (out == {a[2:0],1'b0}) else $error("SHL mismatch a=%0h out=%0h", a,out);
          assert (ovf == 1'b0) else $error("ovf must be 0 on SHL");
        end
        4'b0111: begin // SHR
          assert (out == {1'b0,a[3:1]}) else $error("SHR mismatch a=%0h out=%0h", a,out);
          assert (ovf == 1'b0) else $error("ovf must be 0 on SHR");
        end
        default: begin
          assert (out == 4'b0000) else $error("DEFAULT mismatch ctl=%0h out=%0h", ctl,out);
          assert (ovf == 1'b0) else $error("ovf must be 0 on DEFAULT");
        end
      endcase

      // Zero flag consistency and X-propagation checks
      assert (zero == (out == 4'b0000)) else $error("ZERO flag mismatch out=%0h zero=%0b", out,zero);
      assert (!$isunknown({out,zero})) else $error("Output has X/Z: out=%b zero=%b", out,zero);
    end
  end

  // Lightweight coverage (immediate cover statements)
  always @* begin
    if (!$isunknown({ctl,a,b})) begin
      cover (ctl==4'b0000);
      cover (ctl==4'b0001);
      cover (ctl==4'b0010);
      cover (ctl==4'b0011);
      cover (ctl==4'b0100);
      cover (ctl==4'b0101);
      cover (ctl==4'b0110);
      cover (ctl==4'b0111);
      cover (ctl inside {[4'b1000:4'b1111]}); // default path
      cover (zero);
      cover (!zero);
      cover (ctl==4'b0000 && ovf); // add overflow observed
      cover (ctl==4'b0001 && ovf); // sub overflow observed
    end
  end
endmodule

bind four_bit_alu four_bit_alu_sva sva_i();