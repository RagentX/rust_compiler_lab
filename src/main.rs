// Стандартные коллекции нужны для таблицы переменных, меток и семантической проверки.
use std::{collections::{HashMap, HashSet}, env, fs};

// Все типы токенов, которые может распознать лексический анализатор.
#[derive(Debug, Clone, PartialEq)]
enum Kind {
    Int, If, Else, While, Print, Ident, Number,
    Assign, Plus, Minus, Mul, Div, Eq, Ne, Lt, Gt, Le, Ge,
    Semicolon, LParen, RParen, LBrace, RBrace, Eof,
}

// Один токен хранит тип, текст и позицию в исходном файле.
#[derive(Debug, Clone)]
struct Token { kind: Kind, value: String, line: usize, col: usize }

// Лексер последовательно проходит по симвлам исходной программы.
struct Lexer { chars: Vec<char>, pos: usize, line: usize, col: usize }
impl Lexer {
    fn new(s: &str) -> Self { Self { chars: s.chars().collect(), pos: 0, line: 1, col: 1 } }
    // Текущий символ.
    fn cur(&self) -> Option<char> { self.chars.get(self.pos).copied() }
    // Следующий символ нужен для ==, !=, <=, >= и комментариев.
    fn peek(&self) -> Option<char> { self.chars.get(self.pos + 1).copied() }
    // Переходим к следующему символу и обновляем номер строки и столбца.
    fn advance(&mut self) {
        if let Some(c) = self.cur() {
            self.pos += 1;
            if c == '\n' { self.line += 1; self.col = 1; } else { self.col += 1; }
        }
    }
    fn token(&self, kind: Kind, value: String, line: usize, col: usize) -> Token {
        Token { kind, value, line, col }
    }
    // Главный проход лексера: превращает исходный текст в список токенов.
    fn tokenize(&mut self) -> Result<Vec<Token>, String> {
        let mut out = Vec::new();
        while let Some(c) = self.cur() {
            if c.is_whitespace() { self.advance(); continue; }
            if c == '/' && self.peek() == Some('/') {
                while self.cur().is_some() && self.cur() != Some('\n') { self.advance(); }
                continue;
            }
            let (line, col) = (self.line, self.col);
            if c.is_alphabetic() || c == '_' {
                let mut s = String::new();
                while let Some(x) = self.cur() {
                    if x.is_alphanumeric() || x == '_' { s.push(x); self.advance(); } else { break; }
                }
                let k = match s.as_str() {
                    "int"=>Kind::Int, "if"=>Kind::If, "else"=>Kind::Else,
                    "while"=>Kind::While, "print"=>Kind::Print, _=>Kind::Ident
                };
                out.push(self.token(k, s, line, col)); continue;
            }
            if c.is_ascii_digit() {
                let mut s = String::new();
                while let Some(x) = self.cur() {
                    if x.is_ascii_digit() { s.push(x); self.advance(); } else { break; }
                }
                out.push(self.token(Kind::Number, s, line, col)); continue;
            }
            let two = match (c, self.peek()) {
                ('=',Some('='))=>Some(Kind::Eq), ('!',Some('='))=>Some(Kind::Ne),
                ('<',Some('='))=>Some(Kind::Le), ('>',Some('='))=>Some(Kind::Ge), _=>None
            };
            if let Some(k) = two {
                let v = format!("{}{}", c, self.peek().unwrap());
                self.advance(); self.advance(); out.push(self.token(k, v, line, col)); continue;
            }
            let k = match c {
                '='=>Kind::Assign, '+'=>Kind::Plus, '-'=>Kind::Minus, '*'=>Kind::Mul, '/'=>Kind::Div,
                '<'=>Kind::Lt, '>'=>Kind::Gt, ';'=>Kind::Semicolon, '('=>Kind::LParen, ')'=>Kind::RParen,
                '{'=>Kind::LBrace, '}'=>Kind::RBrace,
                _=>return Err(format!("Лексическая ошибка: неизвестный символ '{}' ({}:{})", c,line,col))
            };
            self.advance(); out.push(self.token(k, c.to_string(), line, col));
        }
        out.push(Token { kind: Kind::Eof, value:"EOF".into(), line:self.line, col:self.col });
        Ok(out)
    }
}

// Узлы выражений в абстрактном синтаксическом дереве.
#[derive(Debug, Clone)]
enum Expr { Num(i64), Id(String), Bin(Box<Expr>, String, Box<Expr>) }
// Основные операторы поддерживаемого языка.
#[derive(Debug, Clone)]
enum Stmt {
    Decl(String), Assign(String, Expr), Print(Expr),
    If(Expr, Vec<Stmt>, Option<Vec<Stmt>>), While(Expr, Vec<Stmt>), Block(Vec<Stmt>)
}

// Рекурсивный нисходящий синтаксический анализатор.
struct Parser { t: Vec<Token>, p: usize }
impl Parser {
    fn new(t: Vec<Token>) -> Self { Self{t,p:0} }
    fn cur(&self)->&Token { &self.t[self.p] }
    fn is(&self,k:&Kind)->bool { &self.cur().kind==k }
    fn take(&mut self,k:Kind)->Result<Token,String>{
        let x=self.cur().clone();
        if x.kind!=k { return Err(format!("Синтаксическая ошибка {}:{}: ожидалось {:?}, получено {:?} '{}'",x.line,x.col,k,x.kind,x.value)); }
        self.p+=1; Ok(x)
    }
    // Разбираем программу целиком до токена EOF.
    fn parse(&mut self)->Result<Vec<Stmt>,String>{ let v=self.list()?; self.take(Kind::Eof)?; Ok(v) }
    fn list(&mut self)->Result<Vec<Stmt>,String>{
        let mut v=vec![]; while !self.is(&Kind::Eof)&&!self.is(&Kind::RBrace){v.push(self.stmt()?);} Ok(v)
    }
    // Выбираем правило грамматики по текущему токену.
    fn stmt(&mut self)->Result<Stmt,String>{
        if self.is(&Kind::Int){ self.take(Kind::Int)?; let n=self.take(Kind::Ident)?.value; self.take(Kind::Semicolon)?; return Ok(Stmt::Decl(n)); }
        if self.is(&Kind::Ident){ let n=self.take(Kind::Ident)?.value; self.take(Kind::Assign)?; let e=self.expr()?; self.take(Kind::Semicolon)?; return Ok(Stmt::Assign(n,e)); }
        if self.is(&Kind::Print){ self.take(Kind::Print)?; let e=self.expr()?; self.take(Kind::Semicolon)?; return Ok(Stmt::Print(e)); }
        if self.is(&Kind::While){ self.take(Kind::While)?; self.take(Kind::LParen)?; let c=self.cond()?; self.take(Kind::RParen)?; return Ok(Stmt::While(c,self.block()?)); }
        if self.is(&Kind::If){
            self.take(Kind::If)?; self.take(Kind::LParen)?; let c=self.cond()?; self.take(Kind::RParen)?;
            let a=self.block()?; let b=if self.is(&Kind::Else){self.take(Kind::Else)?;Some(self.block()?)}else{None};
            return Ok(Stmt::If(c,a,b));
        }
        if self.is(&Kind::LBrace){return Ok(Stmt::Block(self.block()?));}
        Err(format!("Синтаксическая ошибка {}:{}: неожиданный токен '{}'",self.cur().line,self.cur().col,self.cur().value))
    }
    fn block(&mut self)->Result<Vec<Stmt>,String>{self.take(Kind::LBrace)?;let v=self.list()?;self.take(Kind::RBrace)?;Ok(v)}
    // Условие состоит из двух выражений и операции сравнения.
    fn cond(&mut self)->Result<Expr,String>{
        let l=self.expr()?; let op=self.cur().value.clone();
        if !matches!(self.cur().kind,Kind::Eq|Kind::Ne|Kind::Lt|Kind::Gt|Kind::Le|Kind::Ge){return Err("Ожидался оператор сравнения".into());}
        self.p+=1; let r=self.expr()?; Ok(Expr::Bin(Box::new(l),op,Box::new(r)))
    }
    // Сложение и вычитание имеют меньший приоритет.
    fn expr(&mut self)->Result<Expr,String>{
        let mut n=self.term()?; while matches!(self.cur().kind,Kind::Plus|Kind::Minus){let op=self.cur().value.clone();self.p+=1;let r=self.term()?;n=Expr::Bin(Box::new(n),op,Box::new(r));} Ok(n)
    }
    // Умножение и деление имеют больший приоритет.
    fn term(&mut self)->Result<Expr,String>{
        let mut n=self.factor()?; while matches!(self.cur().kind,Kind::Mul|Kind::Div){let op=self.cur().value.clone();self.p+=1;let r=self.factor()?;n=Expr::Bin(Box::new(n),op,Box::new(r));} Ok(n)
    }
    // Простейший элемент выражения: число, переменная или скобки.
    fn factor(&mut self)->Result<Expr,String>{
        if self.is(&Kind::Number){return Ok(Expr::Num(self.take(Kind::Number)?.value.parse().unwrap()));}
        if self.is(&Kind::Ident){return Ok(Expr::Id(self.take(Kind::Ident)?.value));}
        if self.is(&Kind::LParen){self.take(Kind::LParen)?;let e=self.expr()?;self.take(Kind::RParen)?;return Ok(e);}
        Err(format!("Ожидалось число, идентификатор или выражение, получено '{}'",self.cur().value))
    }
}

// Проверяем, что все использованные в выражении переменные объявлены.
fn check_expr(e:&Expr,s:&HashSet<String>)->Result<(),String>{
    match e { Expr::Num(_)=>Ok(()), Expr::Id(n)=>if s.contains(n){Ok(())}else{Err(format!("Семантическая ошибка: переменная '{}' не объявлена",n))},
        Expr::Bin(a,_,b)=>{check_expr(a,s)?;check_expr(b,s)} }
}
// Семантический анализ проверяет объявления и использование переменных.
fn semantic(v:&[Stmt],s:&mut HashSet<String>)->Result<(),String>{
    for x in v { match x {
        Stmt::Decl(n)=>{if !s.insert(n.clone()){return Err(format!("Семантическая ошибка: повторное объявление '{}'",n));}},
        Stmt::Assign(n,e)=>{if !s.contains(n){return Err(format!("Семантическая ошибка: переменная '{}' не объявлена",n));}check_expr(e,s)?;},
        Stmt::Print(e)=>check_expr(e,s)?, Stmt::While(c,b)=>{check_expr(c,s)?;semantic(b,s)?;},
        Stmt::If(c,a,b)=>{check_expr(c,s)?;semantic(a,s)?;if let Some(b)=b{semantic(b,s)?;}},
        Stmt::Block(b)=>semantic(b,s)?,
    }} Ok(())
}

// Генератор промежуточного трехадресного кода.
struct Gen { ir:Vec<String>, temp:usize, label:usize }
impl Gen {
    fn new()->Self{Self{ir:vec![],temp:0,label:0}}
    // Создаем имя временной переменной.
    fn nt(&mut self)->String{self.temp+=1;format!("t{}",self.temp)}
    // Создаем новую метку для переходов.
    fn nl(&mut self)->String{self.label+=1;format!("L{}",self.label)}
    // Переводим выражение AST в последовательность IR-инструкций.
    fn ex(&mut self,e:&Expr)->String{match e{Expr::Num(n)=>n.to_string(),Expr::Id(n)=>n.clone(),Expr::Bin(a,o,b)=>{let l=self.ex(a);let r=self.ex(b);let t=self.nt();self.ir.push(format!("{t} = {l} {o} {r}"));t}}}
    // Генерируем IR для операторов программы.
    fn stmts(&mut self,v:&[Stmt]){for s in v{match s{
        Stmt::Decl(n)=>self.ir.push(format!("DECLARE {n}")),
        Stmt::Assign(n,e)=>{let x=self.ex(e);self.ir.push(format!("{n} = {x}"));},
        Stmt::Print(e)=>{let x=self.ex(e);self.ir.push(format!("PRINT {x}"));},
        Stmt::Block(b)=>self.stmts(b),
        Stmt::While(c,b)=>{let a=self.nl();let z=self.nl();self.ir.push(format!("LABEL {a}"));let x=self.ex(c);self.ir.push(format!("IF_FALSE {x} GOTO {z}"));self.stmts(b);self.ir.push(format!("GOTO {a}"));self.ir.push(format!("LABEL {z}"));},
        Stmt::If(c,a,b)=>{let el=self.nl();let en=self.nl();let x=self.ex(c);self.ir.push(format!("IF_FALSE {x} GOTO {el}"));self.stmts(a);self.ir.push(format!("GOTO {en}"));self.ir.push(format!("LABEL {el}"));if let Some(b)=b{self.stmts(b)}self.ir.push(format!("LABEL {en}"));},
    }}}
}

// Выполняем арифметическую операцию или сравнение.
fn calc(a:i64,o:&str,b:i64)->Result<i64,String>{Ok(match o{"+"=>a+b,"-"=>a-b,"*"=>a*b,"/"=>{if b==0{return Err("Деление на ноль".into())}a/b},"=="=>(a==b)as i64,"!="=>(a!=b)as i64,"<"=>(a<b)as i64,">"=>(a>b)as i64,"<="=>(a<=b)as i64,">="=>(a>=b)as i64,_=>return Err(format!("Неизвестная операция {o}"))})}
// Простая оптимизация: вычисляем операции над двумя константами заранее.
fn optimize(ir:&[String])->Vec<String>{
    ir.iter().map(|x|{let p:Vec<_>=x.split_whitespace().collect();if p.len()==5&&p[1]=="="{if let(Ok(a),Ok(b))=(p[2].parse::<i64>(),p[4].parse::<i64>()){if let Ok(v)=calc(a,p[3],b){return format!("{} = {}",p[0],v)}}}x.clone()}).collect()
}
// Получаем число напрямую или значение переменной из памяти интерпретатора.
fn value(s:&str,m:&HashMap<String,i64>)->Result<i64,String>{s.parse().ok().or_else(||m.get(s).copied()).ok_or_else(||format!("Неизвестное значение '{s}'"))}
// Интерпретатор выполняет готовые IR-инструкции.
fn run(ir:&[String])->Result<Vec<i64>,String>{
    let mut labels=HashMap::new();for(i,x)in ir.iter().enumerate(){let p:Vec<_>=x.split_whitespace().collect();if p.len()==2&&p[0]=="LABEL"{labels.insert(p[1].to_string(),i);}}
    let(mut m,mut out,mut ip)=(HashMap::new(),vec![],0usize);
    while ip<ir.len(){let p:Vec<_>=ir[ip].split_whitespace().collect();
        if p[0]=="DECLARE"{m.insert(p[1].to_string(),0);}
        else if p[0]=="PRINT"{out.push(value(p[1],&m)?);}
        else if p[0]=="LABEL"{}
        else if p[0]=="GOTO"{ip=*labels.get(p[1]).ok_or("Неизвестная метка")?;continue;}
        else if p[0]=="IF_FALSE"{if value(p[1],&m)?==0{ip=*labels.get(p[3]).ok_or("Неизвестная метка")?;continue;}}
        else if p.len()==3&&p[1]=="="{let v=value(p[2],&m)?;m.insert(p[0].to_string(),v);}
        else if p.len()==5&&p[1]=="="{let v=calc(value(p[2],&m)?,p[3],value(p[4],&m)?)?;m.insert(p[0].to_string(),v);}
        else{return Err(format!("Неизвестная IR-инструкция: {}",ir[ip]));} ip+=1;
    } Ok(out)
}

// Перевод IR в простой листинг x86.
fn generate_x86(ir: &[String]) -> Vec<String> {
    let mut out = vec!["section .text".into(), "global _start".into(), "_start:".into()];
    for line in ir {
        let p: Vec<_> = line.split_whitespace().collect();
        if p.is_empty() { continue; }
        if p[0] == "DECLARE" { out.push(format!("    ; variable {}", p[1])); }
        else if p[0] == "LABEL" { out.push(format!("{}:", p[1])); }
        else if p[0] == "GOTO" { out.push(format!("    jmp {}", p[1])); }
        else if p[0] == "IF_FALSE" {
            out.push(format!("    cmp {}, 0", p[1]));
            out.push(format!("    je {}", p[3]));
        } else if p[0] == "PRINT" { out.push(format!("    ; print {}", p[1])); }
        else if p.len() == 3 && p[1] == "=" {
            out.push(format!("    mov eax, {}", p[2]));
            out.push(format!("    mov {}, eax", p[0]));
        } else if p.len() == 5 && p[1] == "=" {
            out.push(format!("    mov eax, {}", p[2]));
            match p[3] {
                "+" => out.push(format!("    add eax, {}", p[4])),
                "-" => out.push(format!("    sub eax, {}", p[4])),
                "*" => out.push(format!("    imul eax, {}", p[4])),
                "/" => { out.push("    cdq".into()); out.push(format!("    idiv {}", p[4])); }
                op => {
                    out.push(format!("    cmp eax, {}", p[4]));
                    let cc=match op {"=="=>"sete","!="=>"setne","<"=>"setl",">"=>"setg","<="=>"setle",">="=>"setge",_=>"sete"};
                    out.push(format!("    {} al",cc));
                    out.push("    movzx eax, al".into());
                }
            }
            out.push(format!("    mov {}, eax",p[0]));
        }
    }
    out.push("    mov eax, 1".into());
    out.push("    xor ebx, ebx".into());
    out.push("    int 0x80".into());
    out
}

// Вспомогательный вывод дерева с отступами.
fn print_ast(v:&[Stmt],d:usize){for s in v{println!("{}{:?}","  ".repeat(d),s);}}
// Точка входа: запускает все этапы компиляции по порядку.
fn main(){
    let file=env::args().nth(1).unwrap_or_else(||"program.txt".into());
    let source=match fs::read_to_string(&file){Ok(x)=>x,Err(e)=>{eprintln!("Не удалось прочитать {file}: {e}");return;}};

    let result=(||->Result<(),String>{
        // Разбиваем исходный текст на лексемы.
        let mut lx=Lexer::new(&source);
        let tokens=lx.tokenize()?;
        let mut report=String::new();

        report.push_str("=== Таблица лексем ===\n");
        report.push_str(&format!("{:<7} {:<7} {:<15} {:<15} {}\n","Строка","Поз.","Имя","Класс","Значение"));
        for t in &tokens {
            if t.kind!=Kind::Eof {
                report.push_str(&format!("{:<7} {:<7} {:<15} {:<15?} {}\n",t.line,t.col,t.value,t.kind,t.value));
            }
        }

        // Проверяем синтаксис и использование переменных.
        let mut p=Parser::new(tokens);
        let ast=p.parse()?;
        semantic(&ast,&mut HashSet::new())?;

        // Получаем IR и затем оптимизирум его.
        let mut g=Gen::new();
        g.stmts(&ast);

        report.push_str("\n=== IR до оптимизации ===\n");
        for(i,x)in g.ir.iter().enumerate(){report.push_str(&format!("{i:03}: {x}\n"));}

        let opt=optimize(&g.ir);
        report.push_str("\n=== IR после оптимизации ===\n");
        for(i,x)in opt.iter().enumerate(){report.push_str(&format!("{i:03}: {x}\n"));}

        // Формируем простой x86-подобный листинг.
        report.push_str("\n=== Код x86 ===\n");
        for x in generate_x86(&opt){report.push_str(&x);report.push('\n');}

        fs::write("output.txt",report).map_err(|e|format!("Не удалось записать output.txt: {e}"))?;
        println!("Готово. Результаты записаны в output.txt");
        Ok(())
    })();

    if let Err(e)=result{eprintln!("\nОшибка компиляции: {e}");}
}
