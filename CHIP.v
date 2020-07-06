// Your code
module control(
    OpCode, //Instruction[6:0]
    ALUOp,  //to ALUctl
    RegWrite,
    ALUSrc1, 
    ALUSrc2,
    IsBEQ,
    IsJAL,
    IsJALR,
    MemRW,
    MemtoReg,
    ImmGenOp);
    // Definition of ports
    input  [6:0]  OpCode;

    output [1:0]  ALUOp;
    output        RegWrite;
    output        ALUSrc1;
    output        ALUSrc2;
    output        IsBEQ;
    output        IsJAL;
    output        IsJALR;
    output        MemRW;
    output [1:0]  MemtoReg;//00:alu 01:data mem 10:PC+4
    output [2:0]  ImmGenOp;

    parameter Rtype = 7'b0110011;//add, sub, include MUL
    parameter Itype = 7'b0010011;//addi, slti   
    parameter LW    = 7'b0000011;
    parameter SW    = 7'b0100011;
    parameter BEQ   = 7'b1100011;
    parameter JAL   = 7'b1101111;
    parameter JALR  = 7'b1100111;
    parameter AUIPC = 7'b0010111;

    //reg  [ 6:0] in_op;
    reg  [2:0] immgenop;
    reg  [1:0] aluop,  memtoreg;
    reg        regwrite, alusrc1, alusrc2, beq, jal, jalr, memrw;

    // Todo 5: wire assignments
    assign ALUOp    = aluop;
    assign RegWrite = regwrite;
    assign ALUSrc1  = alusrc1;
    assign ALUSrc2  = alusrc2;
    assign IsBEQ    = beq;
    assign IsJAL    = jal;
    assign IsJALR   = jalr;    
    assign MemRW    = memrw;
    assign MemtoReg = memtoreg;
    assign ImmGenOp = immgenop;

    // Combinational always block
    always @(*) begin
        case(OpCode)
            Rtype:  aluop = 2'b10;
            Itype:  aluop = 2'b11;
            BEQ  :  aluop = 2'b01;
            default:aluop = 2'b00;
        endcase
        
        regwrite = ((OpCode==SW)||(OpCode==BEQ))? 0:1;
        alusrc1  = (OpCode==AUIPC)? 1:0;
        alusrc2  = ((OpCode==Rtype)||(OpCode==BEQ))? 0:1;
        memrw    = (OpCode==SW   )? 1:0;

        beq      = (OpCode==BEQ  )? 1:0;
        jal      = (OpCode==JAL  )? 1:0;
        jalr     = (OpCode==JALR )? 1:0;

        case(OpCode)
            LW   :  memtoreg = 2'b01;
            JAL  :  memtoreg = 2'b10;
            JALR :  memtoreg = 2'b10;
            default:memtoreg = 2'b00;
        endcase 

        case(OpCode)
            Itype:  immgenop = 3'b000;
            LW   :  immgenop = 3'b000;
            SW   :  immgenop = 3'b001; // s-type
            BEQ  :  immgenop = 3'b010; // sb-type
            JAL  :  immgenop = 3'b011; // uj-type
            JALR :  immgenop = 3'b000; // i-type
            default:immgenop = 3'b111;
        endcase
    end
endmodule 

module ALUControl(ALUOp, Funct, ALUCtl, MULValid, ShiftCtl, Src);
	input   [1:0] ALUOp ;
	input   [4:0] Funct ; // Instruction[30, 25, 14:12]
	output  reg [3:0] ALUCtl;
	output  reg       MULValid;
    output  reg [1:0] ShiftCtl;
    output  reg [1:0] Src;
	always @(*) begin
        MULValid = 0;
		case (ALUOp)
            2'b00:begin
                ALUCtl = 4'b0010;
                ShiftCtl = 2'b00;
                Src=2'b01;
            end
            2'b01:begin
                ALUCtl = 4'b0110;
                ShiftCtl = 2'b00;
                Src=(Funct[2:0]==3'b000)?2'b01:2'b00;                
            end
			2'b11: begin //Itype
                ALUCtl = 4'b0010; // lw, sw -> add  

                case (Funct[2:0])
                    3'b000:begin //addi
                        ALUCtl   = 4'b0010;
                        ShiftCtl = 2'b00;
                        Src      = 2'b01;
                    end
                    3'b010:begin //slti
                        ALUCtl   = 4'b0110;
                        ShiftCtl = 2'b00; 
                        Src      = 2'b00;
                    end                       
                    3'b001:begin // slli
                        ShiftCtl = 2'b00;
                        Src      = 2'b11;
                    end
                    3'b101:begin
                        ShiftCtl = (Funct[4]==0)?2'b01:2'b11; // srli or srai
                        Src      = 2'b11;
                    end
                    default:begin
                        ShiftCtl = 2'b00; 
                        Src      = 2'b11;
                    end
                endcase

            end

            2'b10: begin // R-type
                Src = 2'b01;
                ShiftCtl = 2'b00; 
                case (Funct)
                    5'b00000: ALUCtl = 4'b0010; // add
                    5'b10000: ALUCtl = 4'b0110; // subtract
                    5'b00111: ALUCtl = 4'b0000; // AND
                    5'b00110: ALUCtl = 4'b0001; // OR
                    5'b01000:begin
                        ALUCtl = 4'b0010;
                        MULValid = 1; // MUL
                        Src = 2'b10;
                    end
                    default: ALUCtl = 4'b0010;
                endcase
            end
            default: begin
                ALUCtl = 4'b0010;
                Src = 2'b01;
                ShiftCtl = 2'b01; 
            end
        endcase
    end
endmodule

module shift(
    shiftctrl,
    rs1,
    in_2, // instruction[24:20]
    shift_out);

    input [1:0]  shiftctrl;
    input signed [31:0] rs1;
    input [31:0] in_2;
    output[31:0] shift_out;


    parameter sl  = 2'b00;
    parameter sr  = 2'b01;
    parameter sra = 2'b11;

    reg   [31:0] out;

    assign shift_out=out;

    always @(*) begin
        case(shiftctrl)
            sl :    out = rs1<<in_2;
            sr :    out = rs1>>in_2;
            sra:    out = rs1>>>in_2;
            default:out =0;
        endcase
    end
endmodule

module ALU(alu_in1,alu_in2,zero,alu_result,alu_control,sign);

	//Definition of ports
	input [3:0] alu_control;
	input [31:0] alu_in1,alu_in2;
	output zero;
	output[31:0] alu_result;
    output sign;

	assign alu_result = (alu_control==4'b0000)?(alu_in1 & alu_in2):
	             		(alu_control==4'b0001)?(alu_in1 | alu_in2):
				 		(alu_control==4'b0010)?(alu_in1 + alu_in2):
				 		(alu_control==4'b0110)?(alu_in1 - alu_in2):32'b0;

	assign zero = (alu_result == 32'b0)?1:0;

    assign sign = alu_result[31];

endmodule

module ImmGen(
    ImmGenOp,
    Inst,
    Imm
);
    input [2:0]  ImmGenOp;
    input [31:0] Inst;
    output[31:0] Imm;

    parameter I =3'b000;
    parameter S =3'b001;
    parameter SB=3'b010;
    parameter UJ=3'b011;
    parameter U =3'b100;

    reg   [31:0] out;

    assign Imm=out;

    always @(*) begin
        case(ImmGenOp)
            I :     out={{21{Inst[31]}}, Inst[30:20]};
            S :     out={{21{Inst[31]}}, Inst[30:25], Inst[11:7]};
            SB:     out={{20{Inst[31]}}, Inst[7],     Inst[30:25], Inst[11:8],  1'b0};
            UJ:     out={{12{Inst[31]}}, Inst[19:12], Inst[20],    Inst[30:21], 1'b0};
            U :     out={Inst[31:12],    {12{1'b0}} };
            default:out=0;
        endcase
    end
endmodule

module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I);

    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    wire   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    reg    [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg   
    reg    [ 6:0] OpCode;
    always @(*) begin
        OpCode  = mem_rdata_I[6:0];
        rd      = mem_rdata_I[11: 7];
        rs1     = mem_rdata_I[19:15];
	    rs2     = mem_rdata_I[24:20];
    end
    wire    [ 1:0] ALUOp;
    wire           ALUSrc1; // 1: is auipc
    wire           ALUSrc2; // 0: is r-type
    wire           IsBEQ;
    wire           IsJAL;
    wire           IsJALR;
    wire           MemRW;
    wire   [ 1:0]  MemtoReg;
    wire   [ 2:0]  ImmGenOp; 
    wire   [ 4:0]  Funct;
    assign Funct = {mem_rdata_I[30], mem_rdata_I[25], mem_rdata_I[14:12]};
    wire    [ 3:0] ALUCtl;
    wire           MULValid;
    wire    [ 1:0] ShiftCtl;

    wire    [31:0] A;
    wire   [31:0] B;
    wire   [31:0] ImmGenout;
    assign A = (ALUSrc1) ? PC : rs1_data;
    assign B = (ALUSrc2) ? ImmGenout : rs2_data;
    wire   [31:0] Shiftout;
    wire          done;
    wire          sign;
    wire          Zero;
    wire   [ 1:0] set;
    wire   [31:0] ALUout;
    wire   [31:0] ALUResult;
    wire   [63:0] MULout;
 
    control ctl0(
        .OpCode(OpCode),
        .ALUOp(ALUOp),
        .RegWrite(regWrite),
        .ALUSrc1(ALUSrc1),
        .ALUSrc2(ALUSrc2),
        .IsBEQ(IsBEQ),
        .IsJAL(IsJAL),
        .IsJALR(IsJALR),
        .MemRW(MemRW),
        .MemtoReg(MemtoReg),
        .ImmGenOp(ImmGenOp));

    wire    [31:0] PC_4;        // use PC+4 for many operations -> set a wire for PC+4
    assign PC_4 = PC + 32'd4;

    assign mem_wen_D   = MemRW;
    assign mem_addr_D  = ALUout; // when addr is used -> must be add/sub
    assign mem_wdata_D = rs2_data;
    assign mem_addr_I  = PC;

    assign ALUResult = (set==2'b00) ? sign : 
                       (set==2'b01) ? ALUout : 
                       (set==2'b10) ? MULout[31:0] : Shiftout ;

    assign rd_data = (MemtoReg==2'b00) ? ALUResult   :
                     (MemtoReg==2'b01) ? mem_rdata_D :
                     (MemtoReg==2'b10) ? PC_4        : 0;

    ALUControl aluctl0(
        .ALUOp(ALUOp),
	    .Funct(Funct), // Instruction[30, 25, 14:12]
	    .ALUCtl(ALUCtl),
	    .MULValid(MULValid),
        .ShiftCtl(ShiftCtl),
        .Src(set));

    ImmGen imm0(
        .ImmGenOp(ImmGenOp),
        .Inst(mem_rdata_I),
        .Imm(ImmGenout));

    shift sft0(
        .shiftctrl(ShiftCtl),
        .rs1(A),
        .in_2(B), // instruction[24:20]
        .shift_out(Shiftout));

    ALU alu0(
        .alu_in1(A),
        .alu_in2(B),
        .zero(Zero),
        .alu_result(ALUout),
        .alu_control(ALUCtl),
        .sign(sign));

    multDiv mul0(
        .clk(clk),
        .rst_n(rst_n),
        .valid(MULValid), 
        .ready(done), 
        .mode(1'b0), 
        .in_A(A), 
        .in_B(B), 
        .out(MULout));
    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//
    
    // Todo: any combinational/sequential circuit

	assign PC_nxt = (IsJALR) ? ALUResult : ((IsJAL | (IsBEQ & (Zero | (mem_rdata_I[14:12]==3'b101 & !sign))))? PC + ImmGenout : (done==MULValid) ? PC_4 : PC);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            
        end
        else begin
            PC <= PC_nxt;
            
        end
    end
endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module multDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
  
    // Definition of ports
    input         clk, rst_n;
    input         valid, mode; // mode: 0: multu, 1: divu
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 2'b00;
    parameter MULT = 2'b01;
    parameter DIV  = 2'b10;
    parameter OUT  = 2'b11;

    // Todo: Wire and reg
    reg  [ 1:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;
    reg  ready_nxt,ready,m,m_nxt; 
    reg  [31:0] inputA_nxt,inputA,divisor,divisor_nxt,quotient,quotient_nxt;
    reg  [63:0] partial_s,partial_s_nxt,multiplicand,multiplicand_nxt;
    reg  [31:0] remainder,remainder_nxt;

    // Todo 5: wire assignments
    assign out = shreg_nxt;
    //assign out[63:32] = remainder;
    //assign out[31:0] = quotient;

    // Combinational always block
    // Todo 1: State machine
    always @(*) begin
        case(state)
            IDLE: begin 
                ready_nxt = 0;
                m_nxt =0;
                state_nxt = IDLE;
            	if(valid == 1 && mode == 0)
            		state_nxt = MULT;
            	else if (valid == 1 && mode == 1)
            		state_nxt = DIV;
            	else if (valid == 0)
            		state_nxt = IDLE;
            end
            MULT: begin
                if (counter == 31) begin
                    ready_nxt = 1;
                    m_nxt = 0;
            		state_nxt = OUT;
                end 
            	else begin
                    ready_nxt = 0;
                    m_nxt = 0;
                    state_nxt = MULT;
                end
            end
            DIV : begin
                ready_nxt = 0;
            	if (counter == 31) begin
                    ready_nxt = 1;
                    m_nxt = 1;
            		state_nxt = OUT;
                end
            	else begin
                    ready_nxt = 0;
                    m_nxt = 0;
                    state_nxt = DIV;
                end
            end
            OUT : begin
                 m_nxt = 0;
                 ready_nxt = 0;
                 state_nxt = IDLE;
            end
        endcase
    end
    // Todo 2: Counter
    always @(*) begin
    	case(state)
    		IDLE: counter_nxt = 0;
    		OUT : counter_nxt = 0;
    		MULT: counter_nxt = counter + 1;
    		DIV : counter_nxt = counter + 1;
    	endcase
    end

    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            MULT: begin
                alu_in_nxt = in_B;
            end
            DIV: begin
                alu_in_nxt = in_B;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
    	case(state)
    		IDLE: begin
    			inputA_nxt = in_A;
                divisor_nxt = in_B;
                multiplicand_nxt[63:32] = 0;
                multiplicand_nxt[31:0] = in_B;
                remainder_nxt = in_A;
    			//alu_out = 0;
    			partial_s_nxt = 0;
                quotient_nxt = 0;
    		end

    		MULT: begin
                divisor_nxt = divisor;
                quotient_nxt = 0;
                remainder_nxt = 0;
                partial_s_nxt = partial_s;
                inputA_nxt = inputA;
                multiplicand_nxt = multiplicand;

    			if (inputA[0]==0) begin
    				multiplicand_nxt = (multiplicand<<1);
    				inputA_nxt = (inputA>>1);
                    partial_s_nxt = partial_s;
                    remainder_nxt = 0;
    			end

    			else if (inputA[0]==1) begin
                    partial_s_nxt = partial_s + multiplicand;
    				multiplicand_nxt = (multiplicand<<1);
    				inputA_nxt = (inputA>>1);
                    remainder_nxt = 0;
    			end
    		end

    		DIV: begin
                partial_s_nxt = 0;
                multiplicand_nxt = 0;
                inputA_nxt = 0;
                divisor_nxt = divisor;

                if (remainder < divisor) begin
                    quotient_nxt = quotient + 0;
                    remainder_nxt = remainder;

                end
                else if (remainder >= divisor) begin
                    remainder_nxt = remainder - divisor;
                    quotient_nxt = quotient + 1;   			
    			end
                else begin
                    remainder_nxt = 0;
                    quotient_nxt =0;
                end
            end
            OUT: begin
                inputA_nxt = 0;
                multiplicand_nxt = 0;
                remainder_nxt = 0;
                partial_s_nxt = 0;
                quotient_nxt = 0;
                divisor_nxt = 0;
            end
    	endcase
    end 
 
    // Todo 4: Shift register
    always @(*) begin
    	case(state)
    		IDLE: begin
    			if(valid) begin
                    shreg_nxt[31:0] = in_A;
                    shreg_nxt[63:32] = 0;
                end
    			else begin 
                    shreg_nxt = 0;
                end
    		end
    		MULT: begin
    			shreg_nxt = partial_s;
    		end

    		DIV : begin
    			shreg_nxt = {remainder,quotient};
    		end

            OUT: begin
                if (m == 0) begin
                    shreg_nxt = partial_s;
                end
                else if (m == 1) begin
                    shreg_nxt = {remainder,quotient};
                end
            end
    		default: shreg_nxt[63:0] = {32'b0,in_A};
    	endcase
    end

    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            alu_in <=0;
            counter <= 0;
            inputA <= in_A;
            multiplicand[63:32] <= 0;
            multiplicand[31:0] <= in_B;
            remainder <= 0;
            shreg <= 0;
            partial_s <= 0;
            ready <= 0;
            divisor <= in_B;
            quotient <= 0;
            m <= mode;
        end
        else begin
            state <= state_nxt;
            alu_in <= alu_in_nxt;
            counter <= counter_nxt;
            inputA <= inputA_nxt;
            partial_s <= partial_s_nxt;
            multiplicand <= multiplicand_nxt;
            alu_out <= multiplicand_nxt[32:0];
            remainder <= remainder_nxt;
            shreg <= shreg_nxt;
            ready <= ready_nxt;
            divisor <= divisor_nxt;
            quotient <= quotient_nxt;
            m <= m_nxt;
        end
    end
endmodule